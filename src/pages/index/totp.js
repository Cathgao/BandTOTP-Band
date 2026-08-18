var CryptoJS = require("crypto-js");
let timeOffset = 0;

function time() {
  return Math.floor(Date.now() / 1000) + (timeOffset || 0);
}

// Pre-computed Base32 ASCII lookup table for high performance
const base32Lookup = new Int8Array(128).fill(-1);
'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('').forEach((c, i) => {
  base32Lookup[c.charCodeAt(0)] = i;
  base32Lookup[c.toLowerCase().charCodeAt(0)] = i;
});
'234567'.split('').forEach((c, i) => {
  base32Lookup[c.charCodeAt(0)] = 26 + i;
});

// Fast Base32 decoding directly to CryptoJS WordArray
function base32Decode(input) {
  if (!input || typeof input !== 'string') {
    return CryptoJS.lib.WordArray.create([], 0);
  }
  const clean = input.replace(/[\s=-]/g, '');
  let buffer = 0;
  let bitsLeft = 0;
  const words = [];
  let currentWord = 0;
  let wordBits = 0;
  let totalBytes = 0;

  for (let i = 0; i < clean.length; i++) {
    const code = clean.charCodeAt(i);
    const val = code < 128 ? base32Lookup[code] : -1;
    if (val === -1) continue;
    buffer = (buffer << 5) | val;
    bitsLeft += 5;
    if (bitsLeft >= 8) {
      bitsLeft -= 8;
      const byte = (buffer >>> bitsLeft) & 0xff;
      currentWord = (currentWord << 8) | byte;
      wordBits += 8;
      totalBytes++;
      if (wordBits === 32) {
        words.push(currentWord);
        currentWord = 0;
        wordBits = 0;
      }
    }
  }
  if (wordBits > 0) {
    currentWord = (currentWord << (32 - wordBits));
    words.push(currentWord);
  }
  return CryptoJS.lib.WordArray.create(words, totalBytes);
}

// Ensure secret is parsed into WordArray once
function bufferizeSecret(secret) {
  if (!secret) return CryptoJS.lib.WordArray.create([], 0);
  if (typeof secret === 'object' && secret.words && typeof secret.sigBytes === 'number') {
    return secret;
  }
  if (typeof secret === 'string') {
    if (/^[0-9a-f]{40}$/i.test(secret)) {
      return CryptoJS.enc.Hex.parse(secret);
    }
    return base32Decode(secret);
  }
  return secret;
}

// High-performance TOTP implementation with direct bitwise truncation
function TOTP(secret, timeVal) {
  try {
    const wordSecret = bufferizeSecret(secret);
    const counter = timeVal !== undefined ? timeVal : Math.floor(time() / 30);
    const high = Math.floor(counter / 0x100000000);
    const low = counter >>> 0;
    const msg = CryptoJS.lib.WordArray.create([high, low], 8);

    const hmac = CryptoJS.HmacSHA1(msg, wordSecret);
    const words = hmac.words;
    const lastByte = words[4] & 0xff;
    const offset = lastByte & 0x0f;
    const wordIdx = offset >> 2;
    const shift = (offset & 3) * 8;
    let val;
    if (shift === 0) {
      val = words[wordIdx];
    } else {
      val = (words[wordIdx] << shift) | (words[wordIdx + 1] >>> (32 - shift));
    }
    const truncated = val & 0x7fffffff;
    return (truncated % 1000000).toString().padStart(6, '0');
  } catch (e) {
    return '000000';
  }
}

// Steam Guard TOTP implementation
function SteamTotp(secret, timeVal) {
  try {
    const wordSecret = bufferizeSecret(secret);
    const counter = timeVal !== undefined ? timeVal : Math.floor(time() / 30);
    const high = Math.floor(counter / 0x100000000);
    const low = counter >>> 0;
    const msg = CryptoJS.lib.WordArray.create([high, low], 8);

    const hmac = CryptoJS.HmacSHA1(msg, wordSecret);
    const words = hmac.words;
    const lastByte = words[4] & 0xff;
    const offset = lastByte & 0x0f;
    const wordIdx = offset >> 2;
    const shift = (offset & 3) * 8;
    let val;
    if (shift === 0) {
      val = words[wordIdx];
    } else {
      val = (words[wordIdx] << shift) | (words[wordIdx + 1] >>> (32 - shift));
    }
    let fullcode = val & 0x7fffffff;
    const chars = '23456789BCDFGHJKMNPQRTVWXY';
    let code = '';
    for (let i = 0; i < 5; i++) {
      code += chars.charAt(fullcode % 26);
      fullcode = Math.floor(fullcode / 26);
    }
    return code;
  } catch (e) {
    return '-----';
  }
}

export { TOTP, SteamTotp, timeOffset, bufferizeSecret, base32Decode }