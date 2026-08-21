/* WordBank Prep service worker — offline-first app shell */
const VERSION = 'ce16ed5298';
const CACHE = 'wordbank-' + VERSION;
const ASSETS = [
  "./",
  "./index.html",
  "./app.css?v=ce16ed5298",
  "./app.js?v=ce16ed5298",
  "./words.43e7b2491f.json",
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

  // Navigations: try the network briefly so a fresh deploy shows up, fall back to the cached shell.
  if (req.mode === 'navigate') {
    e.respondWith((async () => {
      try {
        const fresh = await fetch(req);
        const cache = await caches.open(CACHE);
        cache.put('./index.html', fresh.clone());
        return fresh;
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
    const hit = await cache.match(req, {ignoreSearch: false});
    if (hit) return hit;
    try {
      const res = await fetch(req);
      if (res && res.status === 200 && res.type === 'basic') cache.put(req, res.clone());
      return res;
    } catch (err) {
      const loose = await cache.match(req, {ignoreSearch: true});
      if (loose) return loose;
      throw err;
    }
  })());
});
