const express = require('express');
const multer = require('multer');
const axios = require('axios');
const Jimp = require('jimp');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const rateLimit = require('express-rate-limit');
const helmet = require('helmet');
const morgan = require('morgan');
const cors = require('cors');
const { v4: uuidv4 } = require('uuid');

const app = express();
const PORT = process.env.PORT || 3000;

const TEMP_DIR = path.join(__dirname, 'temp');
const MAX_UPLOAD_BYTES = 5 * 1024 * 1024; 
const ALLOWED_MIMES = ['image/png', 'image/jpeg', 'image/jpg', 'image/webp'];
const CLEANUP_MINUTES = 15; 
const OUTPUT_TTL_MS = 5000; 

if (!fs.existsSync(TEMP_DIR)) fs.mkdirSync(TEMP_DIR, { recursive: true });

const upload = multer({
  dest: TEMP_DIR,
  limits: { fileSize: MAX_UPLOAD_BYTES },
  fileFilter: (req, file, cb) => {
    if (!ALLOWED_MIMES.includes(file.mimetype)) {
      return cb(new Error('Unsupported file type'), false);
    }
    cb(null, true);
  },
});

app.use(express.static('public'));
app.use(express.json({ limit: '10kb' })); // small JSON bodies only
app.use(express.urlencoded({ extended: true }));
app.use(cors());
app.use(helmet());
app.use(morgan('tiny'));

const limiter = rateLimit({
  windowMs: 60 * 1000, 
  max: 30, 
  standardHeaders: true,
  legacyHeaders: false,
});
app.use(limiter);

// Utilities -----------------------------------------------------------------

function isValidUrl(s) {
  try {
    const u = new URL(s);
    return u.protocol === 'http:' || u.protocol === 'https:';
  } catch {
    return false;
  }
}

function randomTempPath(suffix = '') {
  return path.join(TEMP_DIR, `${Date.now()}_${uuidv4()}${suffix}`);
}

async function downloadImageToTemp(url) {
  const out = randomTempPath('.tmp');
  const resp = await axios.get(url, {
    responseType: 'arraybuffer',
    timeout: 15_000,
    maxContentLength: MAX_UPLOAD_BYTES,
  });
  await fs.promises.writeFile(out, Buffer.from(resp.data));
  return out;
}

async function convertToPngIfNeeded(inputPath) {
  const img = await Jimp.read(inputPath);
  const outPath = randomTempPath('.png');
  await img.rgba(true).writeAsync(outPath);
  return outPath;
}

function scheduleDelete(filePath, delayMs = OUTPUT_TTL_MS) {
  setTimeout(() => {
    fs.unlink(filePath, (err) => { /* ignore errors */ });
  }, delayMs);
}

async function safeUnlink(filePath) {
  try { await fs.promises.unlink(filePath); } catch (e) { /* ignore */ }
}

function deriveKey(passphrase, salt = null) {
  // Derive 32-byte key using PBKDF2
  salt = salt || crypto.randomBytes(16);
  const key = crypto.pbkdf2Sync(passphrase, salt, 200_000, 32, 'sha512'); // slow derivation
  return { key, salt };
}

function encryptAesGcm(plaintextBuffer, passphrase) {
  const { key, salt } = deriveKey(passphrase);
  const iv = crypto.randomBytes(12);
  const cipher = crypto.createCipheriv('aes-256-gcm', key, iv);
  const ciphertext = Buffer.concat([cipher.update(plaintextBuffer), cipher.final()]);
  const tag = cipher.getAuthTag();
  // return structure: salt(16) | iv(12) | tag(16) | ciphertext
  return Buffer.concat([salt, iv, tag, ciphertext]);
}

function decryptAesGcm(encBuffer, passphrase) {
  const salt = encBuffer.slice(0, 16);
  const iv = encBuffer.slice(16, 28);
  const tag = encBuffer.slice(28, 44);
  const ciphertext = encBuffer.slice(44);
  const { key } = deriveKey(passphrase, salt);
  const decipher = crypto.createDecipheriv('aes-256-gcm', key, iv);
  decipher.setAuthTag(tag);
  const pt = Buffer.concat([decipher.update(ciphertext), decipher.final()]);
  return pt;
}

// Stego functions -----------------------------------------------------------
// We'll store payload as: [4 bytes big-endian length][payload bytes]
// Bits are written MSB-first per byte into R,G,B LSBs sequence across pixels.

async function encodeLSBToPngBuffer(pngPath, payloadBuffer) {
  const img = await Jimp.read(pngPath);
  const { width, height, data } = img.bitmap; // data = RGBA bytes (Uint8Array)
  const usableBits = width * height * 3; // R,G,B LSBs only
  const neededBits = (payloadBuffer.length + 4) * 8; // header + payload

  if (neededBits > usableBits) {
    throw new Error(`Message too big for image capacity. Capacity bytes ≈ ${Math.floor(usableBits / 8)}, needed ${(payloadBuffer.length + 4)}`);
  }

  // Build payload with 4-byte big-endian length header
  const header = Buffer.alloc(4);
  header.writeUInt32BE(payloadBuffer.length, 0);
  const full = Buffer.concat([header, payloadBuffer]);

  // write bits
  let bitIndex = 0;
  for (let ptr = 0; ptr < data.length && bitIndex < full.length * 8; ptr += 4) { // step per pixel (RGBA)
    for (let c = 0; c < 3 && bitIndex < full.length * 8; c++) { // R,G,B
      const byteIndex = Math.floor(bitIndex / 8);
      const bitInByte = 7 - (bitIndex % 8); // MSB-first
      const bit = (full[byteIndex] >> bitInByte) & 1;
      data[ptr + c] = (data[ptr + c] & 0xFE) | bit;
      bitIndex++;
    }
  }

  return await img.getBufferAsync(Jimp.MIME_PNG);
}

async function decodeLSBFromPngBuffer(pngPath) {
  const img = await Jimp.read(pngPath);
  const { data } = img.bitmap;
  const bits = [];

  // Read first 32 bits for length
  for (let ptr = 0; ptr < data.length && bits.length < 32; ptr += 4) {
    for (let c = 0; c < 3 && bits.length < 32; c++) {
      bits.push(data[ptr + c] & 1);
    }
  }
  if (bits.length < 32) throw new Error('Image too small or not encoded');

  // Convert header bits MSB-first
  let length = 0;
  for (let i = 0; i < 32; i++) length = (length << 1) | bits[i];

  const totalBits = 32 + length * 8;
  // Read remaining bits
  for (let ptr = Math.ceil(bits.length / 3) * 4; ptr < data.length && bits.length < totalBits; ptr += 4) {
    for (let c = 0; c < 3 && bits.length < totalBits; c++) {
      bits.push(data[ptr + c] & 1);
    }
  }
  if (bits.length < totalBits) throw new Error('Encoded message truncated');

  const payload = Buffer.alloc(length);
  let pos = 32;
  for (let i = 0; i < length; i++) {
    let byte = 0;
    for (let b = 0; b < 8; b++) {
      byte = (byte << 1) | bits[pos++];
    }
    payload[i] = byte;
  }
  return payload;
}

// Routes --------------------------------------------------------------------

/**
 * POST /encode
 * Body: multipart/form-data with either:
 *  - image file (field 'image'), or
 *  - imageUrl (field) pointing to an image
 * JSON fields (form fields): message (string) OR passphrase (optional)
 */
app.post('/encode', upload.single('image'), async (req, res) => {
  let uploadedPath = null;
  let pngPath = null;
  let outputPath = null;

  try {
    const message = req.body.message;
    const passphrase = req.body.passphrase; // optional

    if (!message || typeof message !== 'string' || message.length === 0) {
      return res.status(400).json({ error: 'message (string) is required' });
    }

    // 1) get image (file or URL)
    if (req.file) {
      uploadedPath = req.file.path;
    } else if (req.body.imageUrl && isValidUrl(req.body.imageUrl)) {
      uploadedPath = await downloadImageToTemp(req.body.imageUrl);
    } else {
      return res.status(400).json({ error: 'image file or valid imageUrl is required' });
    }

    // 2) convert to PNG (lossless)
    pngPath = await convertToPngIfNeeded(uploadedPath);

    // 3) prepare payload: UTF-8 bytes, optionally encrypt
    let payloadBuffer = Buffer.from(message, 'utf8');
    if (passphrase && typeof passphrase === 'string' && passphrase.length > 0) {
      payloadBuffer = encryptAesGcm(payloadBuffer, passphrase);
    }

    // 4) capacity check + encode into PNG buffer
    const encodedPngBuffer = await encodeLSBToPngBuffer(pngPath, payloadBuffer);

    // 5) write output to temp and stream back
    outputPath = randomTempPath('_out.png');
    await fs.promises.writeFile(outputPath, encodedPngBuffer);

    // delete input files immediately
    await safeUnlink(uploadedPath);
    if (pngPath && pngPath !== uploadedPath) await safeUnlink(pngPath);

    // Stream file to client; after finish schedule deletion
    res.setHeader('Content-Type', 'image/png');
    res.setHeader('Content-Disposition', 'attachment; filename=encoded.png');

    const readStream = fs.createReadStream(outputPath);
    readStream.pipe(res);

    // When response ends, schedule deletion
    res.on('finish', () => {
      scheduleDelete(outputPath, OUTPUT_TTL_MS);
    });

  } catch (err) {
    console.error('Encode error:', err);
    // cleanup any temp files we created
    if (uploadedPath) await safeUnlink(uploadedPath);
    if (pngPath) await safeUnlink(pngPath);
    if (outputPath) await safeUnlink(outputPath);
    res.status(500).json({ error: err.message || 'Encoding failed' });
  }
});


/**
 * POST /decode
 * Body: multipart/form-data with either:
 *  - image file (field 'image'), or
 *  - imageUrl (field)
 * Optional form field: passphrase (to decrypt if encrypted)
 */
app.post('/decode', upload.single('image'), async (req, res) => {
  let uploadedPath = null;
  let pngPath = null;

  try {
    const passphrase = req.body.passphrase;

    // 1) get image (file or URL)
    if (req.file) {
      uploadedPath = req.file.path;
    } else if (req.body.imageUrl && isValidUrl(req.body.imageUrl)) {
      uploadedPath = await downloadImageToTemp(req.body.imageUrl);
    } else {
      return res.status(400).json({ error: 'image file or valid imageUrl is required' });
    }

    // 2) ensure PNG / read
    pngPath = await convertToPngIfNeeded(uploadedPath);

    // 3) decode payload buffer
    const payloadBuffer = await decodeLSBFromPngBuffer(pngPath);

    // 4) if passphrase provided try decrypt, otherwise return utf8 text
    let message;
    if (passphrase && passphrase.length > 0) {
      try {
        const decrypted = decryptAesGcm(payloadBuffer, passphrase);
        message = decrypted.toString('utf8');
      } catch (de) {
        // wrong passphrase or tampered
        throw new Error('Decryption failed (wrong passphrase or data corrupted)');
      }
    } else {
      message = payloadBuffer.toString('utf8');
    }

    // cleanup inputs
    await safeUnlink(uploadedPath);
    if (pngPath && pngPath !== uploadedPath) await safeUnlink(pngPath);

    // Return JSON (no output file)
    return res.json({ message });

  } catch (err) {
    console.error('Decode error:', err);
    if (uploadedPath) await safeUnlink(uploadedPath);
    if (pngPath) await safeUnlink(pngPath);
    return res.status(500).json({ error: err.message || 'Decoding failed' });
  }
});

// Background cleanup: remove temp files older than CLEANUP_MINUTES
setInterval(async () => {
  try {
    const files = await fs.promises.readdir(TEMP_DIR);
    const now = Date.now();
    for (const f of files) {
      const p = path.join(TEMP_DIR, f);
      try {
        const stat = await fs.promises.stat(p);
        if ((now - stat.mtimeMs) > CLEANUP_MINUTES * 60 * 1000) {
          await safeUnlink(p);
        }
      } catch (_) { /* ignore */ }
    }
  } catch (e) { /* ignore */ }
}, 5 * 60 * 1000); // run every 5 minutes

// Health & info
app.get('/health', (req, res) => res.json({ ok: true, uptime: process.uptime() }));

// global error handler (fallback)
app.use((err, req, res, next) => {
  console.error('Unhandled error:', err);
  res.status(500).json({ error: err.message || 'Server error' });
});

app.listen(PORT, () => console.log(`Beast-mode stego server listening on http://localhost:${PORT}`));
