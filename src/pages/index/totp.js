// 极速无依赖零分配 SHA-1 / HMAC-SHA1 与 TOTP 实现
// 专为嵌入式 JS 引擎（JerryScript / QuickJS / V8）深度优化

// 查表法 Base32 ASCII 映射表（兼容 ES5，无 TypedArray.prototype.fill 依赖）
var base32Lookup = new Array(128);
for (var i = 0; i < 128; i++) {
  base32Lookup[i] = -1;
}
var b32CharsUpper = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
for (var i = 0; i < 26; i++) {
  var code = b32CharsUpper.charCodeAt(i);
  base32Lookup[code] = i;
  base32Lookup[code + 32] = i; // 小写支持
}
for (var i = 0; i < 6; i++) {
  base32Lookup[50 + i] = 26 + i; // '2'..'7'
}

// 高性能 Base32 解码为字节数组
function decodeBase32ToBytes(input) {
  if (!input || typeof input !== 'string') return [];
  var clean = input.replace(/[\s=-]/g, '');
  var buffer = 0;
  var bitsLeft = 0;
  var bytes = [];
  for (var i = 0; i < clean.length; i++) {
    var code = clean.charCodeAt(i);
    var val = code < 128 ? base32Lookup[code] : -1;
    if (val === -1) continue;
    buffer = (buffer << 5) | val;
    bitsLeft += 5;
    if (bitsLeft >= 8) {
      bitsLeft -= 8;
      bytes.push((buffer >>> bitsLeft) & 0xff);
    }
  }
  return bytes;
}

// 十六进制转字节数组
function hexToBytes(hex) {
  var bytes = [];
  for (var i = 0; i < hex.length; i += 2) {
    bytes.push(parseInt(hex.slice(i, i + 2), 16));
  }
  return bytes;
}

// 统一解析密钥为字节数组
function parseSecretBytes(secret) {
  if (!secret) return [];
  if (Array.isArray(secret)) return secret;
  if (typeof secret === 'string') {
    if (/^[0-9a-f]{40}$/i.test(secret)) {
      return hexToBytes(secret);
    }
    return decodeBase32ToBytes(secret);
  }
  return [];
}

// 全局复用内存缓冲区（避免在 JerryScript/嵌入式引擎中反复触发垃圾回收 GC）
var W_SCRATCH = new Array(16);
for (var i = 0; i < 16; i++) W_SCRATCH[i] = 0;
var INNER_H = new Array(5);
var OUTER_H = new Array(5);

// 核心 SHA-1 单块（512位 / 16字）位运算状态压缩
function sha1Block(H, W) {
  var a = H[0], b = H[1], c = H[2], d = H[3], e = H[4];
  for (var i = 0; i < 80; i++) {
    if (i >= 16) {
      var t = W[(i - 3) & 15] ^ W[(i - 8) & 15] ^ W[(i - 14) & 15] ^ W[(i - 16) & 15];
      W[i & 15] = (t << 1) | (t >>> 31);
    }
    var f, k;
    if (i < 20) {
      f = (b & c) | ((~b) & d);
      k = 0x5A827999;
    } else if (i < 40) {
      f = b ^ c ^ d;
      k = 0x6ED9EBA1;
    } else if (i < 60) {
      f = (b & c) | (b & d) | (c & d);
      k = 0x8F1BBCDC;
    } else {
      f = b ^ c ^ d;
      k = 0xCA62C1D6;
    }
    var temp = (((a << 5) | (a >>> 27)) + f + e + k + W[i & 15]) | 0;
    e = d;
    d = c;
    c = (b << 30) | (b >>> 2);
    b = a;
    a = temp;
  }
  H[0] = (H[0] + a) | 0;
  H[1] = (H[1] + b) | 0;
  H[2] = (H[2] + c) | 0;
  H[3] = (H[3] + d) | 0;
  H[4] = (H[4] + e) | 0;
}

// 密钥预计算：将 K ^ ipad 与 K ^ opad 的 SHA-1 内部状态在实例化时一次性计算完毕
// 使得后续每次 TOTP 计算仅需 2 次单块 SHA-1 变换，达到数学极限性能
function precomputeKey(secret) {
  var k = parseSecretBytes(secret);
  var kWords = new Array(16);
  for (var i = 0; i < 16; i++) kWords[i] = 0;
  for (var i = 0; i < k.length && i < 64; i++) {
    kWords[i >> 2] |= (k[i] & 0xff) << (24 - (i & 3) * 8);
  }

  var innerState = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
  for (var i = 0; i < 16; i++) {
    W_SCRATCH[i] = kWords[i] ^ 0x36363636;
  }
  sha1Block(innerState, W_SCRATCH);

  var outerState = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
  for (var i = 0; i < 16; i++) {
    W_SCRATCH[i] = kWords[i] ^ 0x5c5c5c5c;
  }
  sha1Block(outerState, W_SCRATCH);

  return { innerState: innerState, outerState: outerState };
}

// 基于预计算状态的超快速 HMAC-SHA1 截断值提取（零内存分配）
function fastHmacSha1Truncated(prec, counter) {
  // 1. 内部哈希计算：从 innerState 开始处理 8 字节计数器块
  INNER_H[0] = prec.innerState[0];
  INNER_H[1] = prec.innerState[1];
  INNER_H[2] = prec.innerState[2];
  INNER_H[3] = prec.innerState[3];
  INNER_H[4] = prec.innerState[4];

  W_SCRATCH[0] = Math.floor(counter / 0x100000000) | 0;
  W_SCRATCH[1] = counter | 0;
  W_SCRATCH[2] = 0x80000000 | 0;
  for (var i = 3; i < 15; i++) W_SCRATCH[i] = 0;
  W_SCRATCH[15] = 576; // (64 + 8) * 8 = 576 位

  sha1Block(INNER_H, W_SCRATCH);

  // 2. 外部哈希计算：从 outerState 开始处理 20 字节内部哈希结果
  OUTER_H[0] = prec.outerState[0];
  OUTER_H[1] = prec.outerState[1];
  OUTER_H[2] = prec.outerState[2];
  OUTER_H[3] = prec.outerState[3];
  OUTER_H[4] = prec.outerState[4];

  W_SCRATCH[0] = INNER_H[0];
  W_SCRATCH[1] = INNER_H[1];
  W_SCRATCH[2] = INNER_H[2];
  W_SCRATCH[3] = INNER_H[3];
  W_SCRATCH[4] = INNER_H[4];
  W_SCRATCH[5] = 0x80000000 | 0;
  for (var i = 6; i < 15; i++) W_SCRATCH[i] = 0;
  W_SCRATCH[15] = 672; // (64 + 20) * 8 = 672 位

  sha1Block(OUTER_H, W_SCRATCH);

  // 动态截断：提取偏移量并合成 31 位无符号整数
  var lastByte = OUTER_H[4] & 0xff;
  var offset = lastByte & 0x0f;
  var wordIdx = offset >> 2;
  var shift = (offset & 3) * 8;
  var val;
  if (shift === 0) {
    val = OUTER_H[wordIdx];
  } else {
    val = (OUTER_H[wordIdx] << shift) | (OUTER_H[wordIdx + 1] >>> (32 - shift));
  }
  return val & 0x7fffffff;
}

// 快速 TOTP 计算
function fastTOTP(prec, timeVal) {
  try {
    var counter = timeVal !== undefined ? timeVal : Math.floor(Date.now() / 30000);
    var truncated = fastHmacSha1Truncated(prec, counter);
    var num = String(truncated % 1000000);
    while (num.length < 6) num = '0' + num;
    return num;
  } catch (e) {
    return '000000';
  }
}

// 快速 Steam Guard 计算
function fastSteamTotp(prec, timeVal) {
  try {
    var counter = timeVal !== undefined ? timeVal : Math.floor(Date.now() / 30000);
    var fullcode = fastHmacSha1Truncated(prec, counter);
    var chars = '23456789BCDFGHJKMNPQRTVWXY';
    var code = '';
    for (var i = 0; i < 5; i++) {
      code += chars.charAt(fullcode % 26);
      fullcode = Math.floor(fullcode / 26);
    }
    return code;
  } catch (e) {
    return '-----';
  }
}

// 兼容接口：支持直接传入字符串密钥或预计算对象
function TOTP(secret, timeVal) {
  if (secret && secret.innerState) {
    return fastTOTP(secret, timeVal);
  }
  var prec = precomputeKey(secret);
  return fastTOTP(prec, timeVal);
}

function SteamTotp(secret, timeVal) {
  if (secret && secret.innerState) {
    return fastSteamTotp(secret, timeVal);
  }
  var prec = precomputeKey(secret);
  return fastSteamTotp(prec, timeVal);
}

module.exports = {
  TOTP: TOTP,
  SteamTotp: SteamTotp,
  fastTOTP: fastTOTP,
  fastSteamTotp: fastSteamTotp,
  precomputeKey: precomputeKey,
  base32Decode: decodeBase32ToBytes
};