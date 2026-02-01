#!/usr/bin/env node
// bisik-decrypt.mjs — Decrypt Bisik messages offline
//
// Usage:
//   node bisik-decrypt.mjs '{"v":1,"eph":"...","nonce":"...","ct":"..."}'
//
// Or pipe from stdin:
//   echo '{"v":1,...}' | node bisik-decrypt.mjs
//
// Set BISIK_PRIVATE_KEY_D env var, or it will prompt.

const OWNER_PRIV_JWK = {
  kty: 'EC',
  crv: 'P-256',
  x: 'c9IFJxmxFbCoTs-cCbo8RzM3Ola5QSDA8mvrVSB7pTA',
  y: 'HAmH4UvZn3I8IsKsdg-kB8Qgb56GW0-H1oDTy3M0uKk',
  d: process.env.BISIK_PRIVATE_KEY_D || null,
};

function fromB64(s) {
  const bin = atob(s);
  const buf = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) buf[i] = bin.charCodeAt(i);
  return buf;
}

async function decrypt(json) {
  if (!OWNER_PRIV_JWK.d) {
    console.error('Error: Set BISIK_PRIVATE_KEY_D environment variable to your private key "d" value.');
    console.error('Example: BISIK_PRIVATE_KEY_D="ke5IfFRBlmpPcHLKjj66r5NQ_XZG4eLV2ICm3obTNGM" node bisik-decrypt.mjs \'...\'');
    process.exit(1);
  }

  const blob = JSON.parse(json);
  if (blob.v !== 1) throw new Error('Unsupported version: ' + blob.v);

  const cs = crypto.subtle;

  // Import owner private key
  const privKey = await cs.importKey(
    'jwk', { ...OWNER_PRIV_JWK, key_ops: ['deriveBits'] },
    { name: 'ECDH', namedCurve: 'P-256' }, false, ['deriveBits']
  );

  // Import sender's ephemeral public key
  const ephPub = await cs.importKey(
    'raw', fromB64(blob.eph),
    { name: 'ECDH', namedCurve: 'P-256' }, false, []
  );

  // ECDH shared secret
  const shared = await cs.deriveBits({ name: 'ECDH', public: ephPub }, privKey, 256);

  // HKDF → AES-256-GCM key
  const hkdfKey = await cs.importKey('raw', shared, 'HKDF', false, ['deriveKey']);
  const aesKey = await cs.deriveKey(
    { name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(32), info: new TextEncoder().encode('bisik-v1') },
    hkdfKey, { name: 'AES-GCM', length: 256 }, false, ['decrypt']
  );

  // Decrypt
  const nonce = fromB64(blob.nonce);
  const ct = fromB64(blob.ct);
  const pt = await cs.decrypt({ name: 'AES-GCM', iv: nonce }, aesKey, ct);
  const msg = JSON.parse(new TextDecoder().decode(pt));

  console.log('\n--- Bisik Message ---');
  console.log('Name:     ', msg.name || '(anonymous)');
  console.log('Email:    ', msg.email || '(not provided)');
  console.log('Timestamp:', msg.timestamp);
  console.log('Message:  ', msg.message);
  console.log('---');
}

// Read from argument or stdin
let input = process.argv[2];
if (input) {
  decrypt(input);
} else {
  let data = '';
  process.stdin.setEncoding('utf8');
  process.stdin.on('data', (chunk) => data += chunk);
  process.stdin.on('end', () => decrypt(data.trim()));
}
