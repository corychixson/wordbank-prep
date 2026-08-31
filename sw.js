/* WordBank Prep service worker — offline-first app shell */
const VERSION = '53917fcc3f';
const CACHE = 'wordbank-' + VERSION;
const ASSETS = [
  "./",
  "./index.html",
  "./app.css?v=53917fcc3f",
  "./app.js?v=53917fcc3f",
  "./words.43e7b2491f.json",
  "./skills.95e9578aca.json",
  "./manifest.webmanifest",
  "./icon-192.png",
  "./icon-512.png",
  "./icon-maskable-192.png",
  "./icon-maskable-512.png",
  "./apple-touch-icon.png",
  "./icon.svg",
  "./favicon.ico"
];

self.addEventListener('install', e => {
  e.waitUntil((async () => {
    const cache = await caches.open(CACHE);
    await cache.addAll(ASSETS);
  })());
});

self.addEventListener('activate', e => {
  e.waitUntil((async () => {
    const keys = await caches.keys();
    await Promise.all(keys.filter(k => k.startsWith('wordbank-') && k !== CACHE).map(k => caches.delete(k)));
    await self.clients.claim();
  })());
});

self.addEventListener('message', e => {
  if (e.data && e.data.type === 'SKIP_WAITING') self.skipWaiting();
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return;

  // Navigations: network first so a fresh deploy shows up, falling back to the precached shell.
  // The fresh page is deliberately NOT written into this cache: the precache is a consistent
  // versioned set (index.html + the app.js/app.css it references), and mixing a newer page with
  // older scripts is the one way an offline boot could break.
  if (req.mode === 'navigate') {
    e.respondWith((async () => {
      try {
        return await fetch(req);
      } catch (err) {
        const cache = await caches.open(CACHE);
        return (await cache.match('./index.html')) || (await cache.match('./')) || Response.error();
      }
    })());
    return;
  }

  // Everything else: cache first (all app assets are content-versioned), then network.
  e.respondWith((async () => {
    const cache = await caches.open(CACHE);
    const hit = await cache.match(req);
    if (hit) return hit;
    const res = await fetch(req);
    if (res && res.status === 200 && res.type === 'basic') cache.put(req, res.clone());
    return res;
  })());
});
