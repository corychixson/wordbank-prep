/* ============================================================
   Core: data, state, persistence, filters, utilities, shell
   ============================================================ */
'use strict';
const $ = (s, r) => (r || document).querySelector(s);
const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));

const norm = s => s.normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const fmt = n => Number(n).toLocaleString('en-US');
const DAY = 86400000;
const INTERVALS = [0, 1, 3, 7, 14, 30]; // days per box 0..5
const TIER_NAME = {1: 'Core', 2: 'Extended', 3: 'Advanced'};

let RND = Math.random;
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
/* Run fn with a deterministic generator so two devices build the identical quiz. */
function withSeed(seed, fn) {
  const prev = RND; RND = mulberry32(seed);
  try { return fn(); } finally { RND = prev; }
}
function shuffle(a) { const b = a.slice(); for (let i = b.length - 1; i > 0; i--) { const j = Math.floor(RND() * (i + 1)); [b[i], b[j]] = [b[j], b[i]]; } return b; }
function pickRandom(a) { return a[Math.floor(RND() * a.length)]; }
function todayKey(d) { d = d || new Date(); return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') + '-' + String(d.getDate()).padStart(2, '0'); }

/* ---------- Words ---------- */
function primaryPos(pos) { const t = pos.split('/')[0]; if (t.startsWith('adj')) return 'adj'; if (t === 'n.') return 'n'; if (t === 'v.') return 'v'; return 'other'; }
function posSet(pos) { const s = new Set(); pos.split('/').forEach(t => { if (t.startsWith('adj')) s.add('adj'); else if (t === 'n.') s.add('n'); else if (t === 'v.') s.add('v'); else s.add('other'); }); return s; }
let WORDS = [];
let BY_WORD = new Map();
let BY_POS = {adj: [], n: [], v: [], other: []};
let COUNTS = {t1: 0, t2: 0, t3: 0, all: 0, t12: 0};
function initData(RAW) {
  WORDS = RAW.map((r, i) => {
    const key = norm(r[0]);
    return { id: i, w: r[0], pos: r[1], def: r[2], ex: r[3], syn: r[4].split('|'), tier: r[5], tests: r[6], key, letter: key[0], p: primaryPos(r[1]), ps: posSet(r[1]) };
  });
  BY_WORD = new Map(WORDS.map(w => [w.w, w]));
  BY_POS = {adj: [], n: [], v: [], other: []};
  WORDS.forEach(w => BY_POS[w.p].push(w));
  COUNTS = {t1: WORDS.filter(w => w.tier === 1).length, t2: WORDS.filter(w => w.tier === 2).length, t3: WORDS.filter(w => w.tier === 3).length, all: WORDS.length};
  COUNTS.t12 = COUNTS.t1 + COUNTS.t2;
}

/* Find the token in a sentence that corresponds to the headword (handles inflections). Returns [start,end] or null. */
function stemsOf(word) {
  const w = norm(word); const parts = w.split(/[\s-]+/); const first = parts[0];
  const st = [];
  if (parts.length > 1) return {phrase: w, stems: [first]};
  st.push(first);
  if (first.length >= 5) { st.push(first.slice(0, -1)); st.push(first.slice(0, -2)); }
  if (first.length >= 7) st.push(first.slice(0, -3));
  if (first.endsWith('y')) st.push(first.slice(0, -1) + 'i');
  if (first.endsWith('e')) st.push(first.slice(0, -1));
  if (first.endsWith('ify')) st.push(first.slice(0, -3) + 'if');
  return {phrase: null, stems: st};
}
function findWordSpan(sentence, word) {
  const info = stemsOf(word);
  const ns = norm(sentence);
  if (info.phrase) { const i = ns.indexOf(info.phrase); if (i >= 0) return [i, i + info.phrase.length]; }
  const minLen = Math.min(4, norm(word).split(/[\s-]+/)[0].length);
  const re = /[a-z\u00C0-\u024F'\u2019]+/gi; let m, best = null;
  while ((m = re.exec(sentence))) {
    const tok = norm(m[0]);
    for (const s of info.stems) {
      if (s.length >= minLen && tok.startsWith(s)) { if (!best || s.length > best.len) best = {s: m.index, e: m.index + m[0].length, len: s.length}; break; }
    }
  }
  return best ? [best.s, best.e] : null;
}
function highlightWord(entry) {
  const span = findWordSpan(entry.ex, entry.w);
  if (!span) return esc(entry.ex);
  return esc(entry.ex.slice(0, span[0])) + '<b>' + esc(entry.ex.slice(span[0], span[1])) + '</b>' + esc(entry.ex.slice(span[1]));
}
function blankSentence(entry, blank) {
  const span = findWordSpan(entry.ex, entry.w);
  if (!span) return null;
  blank = blank || '<span class="blank">&nbsp;</span>';
  return esc(entry.ex.slice(0, span[0])) + blank + esc(entry.ex.slice(span[1]));
}

/* ---------- State & persistence ---------- */
const KEY = 'satact-vocab-builder-v1';
const DEFAULT_SETTINGS = {theme: null, tiers: [1, 2, 3], test: 'both', letters: null, pos: ['adj', 'n', 'v', 'other'], status: ['new', 'learning', 'known', 'mastered'], welcomed: false, fcDeck: 'smart', fcSize: '20', fcFront: 'word', qType: 'mixed', qCount: '10', mPairs: '6', view: 'flashcards', goal: 20, installDismissed: false, iosHintSeen: false, nickname: ''};
let state = {v: 1, cards: {}, quiz: {attempts: 0, correct: 0}, match: {best: {}}, days: {}, settings: Object.assign({}, DEFAULT_SETTINGS)};
let storageOK = true;
try { localStorage.setItem('__vb_test', '1'); localStorage.removeItem('__vb_test'); } catch (e) { storageOK = false; }
(function load() {
  if (!storageOK) return;
  try {
    const raw = localStorage.getItem(KEY);
    if (raw) { const s = JSON.parse(raw); if (s && s.cards) { state = s; state.settings = Object.assign({}, DEFAULT_SETTINGS, s.settings || {}); state.quiz = s.quiz || {attempts: 0, correct: 0}; state.match = s.match || {best: {}}; state.days = s.days || {}; } }
  } catch (e) { console.warn('Could not load saved progress', e); }
})();
let saveTimer = null;
function save() {
  if (!storageOK) return;
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => { try { localStorage.setItem(KEY, JSON.stringify(state)); } catch (e) { storageOK = false; console.warn('save failed', e); } }, 120);
}
function card(w) { return state.cards[w.w] || null; }
function ensureCard(w) { let c = state.cards[w.w]; if (!c) { c = state.cards[w.w] = {b: 0, d: 0, s: 0, c: 0, x: 0, l: 0}; } return c; }
function statusOf(w) { const c = state.cards[w.w]; if (!c || !c.s) return 'new'; if (c.b >= 5) return 'mastered'; if (c.b >= 3) return 'known'; return 'learning'; }
function isDue(w, now) { const c = state.cards[w.w]; return !!(c && c.s && c.d <= (now || Date.now())); }
function isMissed(w) { const c = state.cards[w.w]; return !!(c && c.x > 0 && c.b < 3); }
function bumpDay() { const k = todayKey(); state.days[k] = (state.days[k] || 0) + 1; if (typeof goalRender === 'function') goalRender(); }
function todayCount() { return state.days[todayKey()] || 0; }
/* Apply a flashcard rating: 'again' | 'hard' | 'good' */
function rateWord(w, rating) {
  const c = ensureCard(w); const now = Date.now();
  c.s++; c.l = now;
  if (rating === 'again') { c.b = 0; c.x++; c.d = now; }
  else if (rating === 'hard') { c.b = Math.max(1, c.b); c.c++; c.d = now + INTERVALS[c.b] * DAY; }
  else { c.b = Math.min(5, c.b + 1); c.c++; c.d = now + INTERVALS[c.b] * DAY; }
  bumpDay(); save();
}
function quizResult(w, correct) {
  const c = ensureCard(w); const now = Date.now();
  c.s++; c.l = now;
  if (correct) { c.c++; if (c.b === 0) { c.b = 1; c.d = now + INTERVALS[1] * DAY; } }
  else { c.x++; c.b = 0; c.d = now; }
  state.quiz.attempts++; if (correct) state.quiz.correct++;
  bumpDay(); save();
}
function setMastered(w) { const c = ensureCard(w); c.s++; c.b = 5; c.d = Date.now() + INTERVALS[5] * DAY; c.l = Date.now(); save(); }
function setReview(w) { const c = ensureCard(w); c.s++; c.b = 0; c.x++; c.d = Date.now(); c.l = Date.now(); save(); }
function resetWord(w) { delete state.cards[w.w]; save(); }

/* ---------- Filters ---------- */
const S = () => state.settings;
function filtered() {
  const s = S(); const tiers = new Set(s.tiers); const letters = s.letters ? new Set(s.letters) : null; const pos = new Set(s.pos); const st = new Set(s.status);
  const allStatus = st.size === 4, allPos = pos.size === 4;
  return WORDS.filter(w => {
    if (!tiers.has(w.tier)) return false;
    if (s.test === 'act' && w.tests !== 0) return false;
    if (letters && !letters.has(w.letter)) return false;
    if (!allPos) { let ok = false; for (const p of w.ps) if (pos.has(p)) { ok = true; break; } if (!ok) return false; }
    if (!allStatus && !st.has(statusOf(w))) return false;
    return true;
  });
}
const filterListeners = [];
function onFilterChange(fn) { filterListeners.push(fn); }
function filtersChanged() { save(); renderFilterBar(); filterListeners.forEach(fn => fn()); }

function renderFilterBar() {
  const s = S();
  $$('#tierChips .chip').forEach(b => { const on = s.tiers.includes(+b.dataset.tier); b.classList.toggle('on', on); b.setAttribute('aria-pressed', on); });
  $$('#testSeg button').forEach(b => b.classList.toggle('on', b.dataset.test === s.test));
  $$('#posRow .chip').forEach(b => { const on = s.pos.includes(b.dataset.pos); b.classList.toggle('on', on); b.setAttribute('aria-pressed', on); });
  $$('#statusRow .chip').forEach(b => { const on = s.status.includes(b.dataset.status); b.classList.toggle('on', on); b.setAttribute('aria-pressed', on); });
  $$('#letterRow .letterchip').forEach(b => { const on = !s.letters || s.letters.includes(b.dataset.letter); b.classList.toggle('on', on); b.setAttribute('aria-pressed', on); });
  $('#letterLbl').textContent = !s.letters ? 'All' : (s.letters.length === 0 ? 'None' : (s.letters.length <= 6 ? s.letters.map(l => l.toUpperCase()).join(' ') : s.letters.length + ' letters'));
  const on = s.pos.length < 4 || s.status.length < 4;
  $('#moreBtn').classList.toggle('on', on);
  $('#filterCount').textContent = fmt(filtered().length);
}
function toggleInList(list, val) { const i = list.indexOf(val); if (i >= 0) list.splice(i, 1); else list.push(val); }
function initFilterBar() {
  $$('[data-count]').forEach(el => { el.textContent = fmt(COUNTS[el.dataset.count]); });
  $('#brandCount').textContent = fmt(COUNTS.all);
  $$('#tierChips .chip').forEach(b => b.addEventListener('click', () => { const t = +b.dataset.tier; const s = S(); toggleInList(s.tiers, t); if (!s.tiers.length) s.tiers.push(t); filtersChanged(); }));
  $$('#testSeg button').forEach(b => b.addEventListener('click', () => { S().test = b.dataset.test; filtersChanged(); }));
  $$('#posRow .chip').forEach(b => b.addEventListener('click', () => { const s = S(); toggleInList(s.pos, b.dataset.pos); if (!s.pos.length) s.pos.push(b.dataset.pos); filtersChanged(); }));
  $$('#statusRow .chip').forEach(b => b.addEventListener('click', () => { const s = S(); toggleInList(s.status, b.dataset.status); if (!s.status.length) s.status.push(b.dataset.status); filtersChanged(); }));
  const row = $('#letterRow');
  'abcdefghijklmnopqrstuvwxyz'.split('').forEach(l => { const b = document.createElement('button'); b.className = 'chip letterchip on'; b.dataset.letter = l; b.textContent = l.toUpperCase(); b.setAttribute('aria-pressed', 'true'); row.appendChild(b); b.addEventListener('click', () => { const s = S(); if (!s.letters) s.letters = 'abcdefghijklmnopqrstuvwxyz'.split(''); toggleInList(s.letters, l); if (s.letters.length === 26) s.letters = null; filtersChanged(); }); });
  $$('#letterPop [data-letters]').forEach(b => b.addEventListener('click', () => { S().letters = b.dataset.letters === 'all' ? null : []; filtersChanged(); }));
  $('#resetFilters').addEventListener('click', () => { const s = S(); s.tiers = [1, 2, 3]; s.test = 'both'; s.letters = null; s.pos = ['adj', 'n', 'v', 'other']; s.status = ['new', 'learning', 'known', 'mastered']; filtersChanged(); toast('Filters reset'); });
  // popovers
  const pops = [['#letterBtn', '#letterPop'], ['#moreBtn', '#morePop']];
  pops.forEach(([bs, ps]) => { $(bs).addEventListener('click', e => { e.stopPropagation(); const p = $(ps); const open = p.hidden; pops.forEach(([b2, p2]) => { $(p2).hidden = true; $(b2).setAttribute('aria-expanded', 'false'); }); p.hidden = !open; $(bs).setAttribute('aria-expanded', String(open)); }); $(ps).addEventListener('click', e => e.stopPropagation()); });
  document.addEventListener('click', () => pops.forEach(([b, p]) => { $(p).hidden = true; $(b).setAttribute('aria-expanded', 'false'); }));
  document.addEventListener('keydown', e => { if (e.key === 'Escape') { pops.forEach(([b, p]) => { $(p).hidden = true; $(b).setAttribute('aria-expanded', 'false'); }); closeModal(); } });
  renderFilterBar();
}

/* ---------- Shell: views, theme, toast, modal ---------- */
const viewListeners = {};
function onShowView(name, fn) { (viewListeners[name] = viewListeners[name] || []).push(fn); }
function showView(name) {
  $$('.tab, .bnav-btn').forEach(t => { const on = t.dataset.view === name; t.classList.toggle('active', on); t.setAttribute('aria-selected', on); });
  $$('.view').forEach(v => v.classList.toggle('active', v.id === 'view-' + name));
  S().view = name; save();
  (viewListeners[name] || []).forEach(fn => fn());
  window.scrollTo({top: 0});
}
function applyTheme() {
  const t = S().theme || (window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
  document.documentElement.setAttribute('data-theme', t);
  $('#themeToggle').textContent = t === 'dark' ? '☀' : '◐';
  const meta = $('#themeColor'); if (meta) meta.setAttribute('content', t === 'dark' ? '#171a24' : '#ffffff');
}
let toastTimer = null;
function toast(msg) { const t = $('#toast'); t.textContent = msg; t.classList.add('show'); clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove('show'), 2200); }
function openModal(html) {
  const root = $('#modalRoot');
  root.innerHTML = '<div class="modal-bg"><div class="modal" role="dialog" aria-modal="true">' + html + '</div></div>';
  const bg = $('.modal-bg', root);
  bg.addEventListener('click', e => { if (e.target === bg) closeModal(); });
  $$('[data-close]', root).forEach(b => b.addEventListener('click', closeModal));
  const first = $('button, [href], input', root); if (first) first.focus();
  return root;
}
function closeModal() { $('#modalRoot').innerHTML = ''; }
function confirmModal(title, body, okLabel, onOk, danger) {
  openModal('<h2>' + esc(title) + '</h2><p>' + body + '</p><div class="row" style="justify-content:flex-end;margin-top:16px"><button class="btn" data-close>Cancel</button><button class="btn ' + (danger ? 'danger' : 'primary') + '" id="confirmOk">' + esc(okLabel) + '</button></div>');
  $('#confirmOk').addEventListener('click', () => { closeModal(); onOk(); });
}
function helpModal() {
  openModal(`
    <h2>How to use WordBank Prep</h2>
    <p>This app contains <b>${fmt(COUNTS.all)}</b> vocabulary words drawn from the major SAT and ACT prep lists plus the "words in context" vocabulary tested on today's digital SAT and ACT. Every entry has a part of speech, a student-friendly definition, an example sentence, and synonyms.</p>
    <h3>Tiers (priority)</h3>
    <ul>
      <li><b>Core</b> (${fmt(COUNTS.t1)} words) — highest-frequency words that appear again and again on the SAT and ACT. Master these first.</li>
      <li><b>Extended</b> (${fmt(COUNTS.t2)}) — words found on standard SAT/ACT prep lists.</li>
      <li><b>Advanced</b> (${fmt(COUNTS.t3)}) — challenging vocabulary for students aiming for top scores.</li>
    </ul>
    <h3>SAT vs. ACT</h3>
    <p>Choose <b>ACT</b> in the filter bar to hide classic hard SAT-list words that are unlikely to matter on the ACT. Choose <b>SAT</b> or <b>SAT &amp; ACT</b> to study everything.</p>
    <h3>Spaced repetition</h3>
    <p>Each word sits in a "box" from 0 to 5. Rate a flashcard <b>Got it</b> and the word moves up a box and comes back later (1, 3, 7, 14, then 30 days). Rate it <b>Missed it</b> and it drops back to box 0 and returns in the same session. Words in boxes 3–4 count as <b>Known</b>; box 5 is <b>Mastered</b>. The <em>Smart review</em> deck always shows due reviews first, then new words.</p>
    <h3>Keyboard shortcuts</h3>
    <ul>
      <li>Flashcards: <kbd>Space</kbd> flip · <kbd>1</kbd> Missed it · <kbd>2</kbd> Hard · <kbd>3</kbd> Got it · <kbd>U</kbd> undo · <kbd>S</kbd> skip</li>
      <li>Quiz: <kbd>1</kbd>–<kbd>4</kbd> choose an answer · <kbd>Enter</kbd> next question</li>
    </ul>
    <h3>Saving your progress</h3>
    <p>${storageOK ? 'Progress is saved automatically on this device. Use <b>Progress → Back up</b> to export it and move it to another phone or computer.' : '<b>Note:</b> this browser is blocking storage, so progress will reset when you close the page.'}</p>
    <h3>Install it on your phone</h3>
    <p>On Android, tap <b>Install app</b> when it appears (or Chrome's ⋮ menu → <i>Install app</i>). On iPhone, tap the <b>Share</b> button in Safari, then <b>Add to Home Screen</b>. Once installed it opens full-screen and <b>works with no internet connection</b>, so you can study anywhere.</p>
    <div class="row" style="justify-content:flex-end;margin-top:16px"><button class="btn primary" data-close>Got it</button></div>`);
}
function haptic(ms) { try { if (navigator.vibrate) navigator.vibrate(ms); } catch (e) {} }
function initShell() {
  $$('.tab, .bnav-btn').forEach(t => t.addEventListener('click', () => { showView(t.dataset.view); haptic(8); }));
  $('#themeToggle').addEventListener('click', () => { const cur = document.documentElement.getAttribute('data-theme'); S().theme = cur === 'dark' ? 'light' : 'dark'; save(); applyTheme(); });
  $('#helpBtn').addEventListener('click', helpModal);
  const fh = $('#footerHelp'); if (fh) fh.addEventListener('click', helpModal);
  $('#filterToggle').addEventListener('click', () => { const fb = $('#filterbar'); const open = !fb.classList.contains('open'); fb.classList.toggle('open', open); $('#filterToggle').setAttribute('aria-expanded', String(open)); $('#filterToggle').textContent = open ? 'Filters ▴' : 'Filters ▾'; });
  applyTheme();
  if (window.matchMedia) window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', applyTheme);
}
function download(filename, text, mime) {
  try {
    const blob = new Blob([text], {type: mime || 'text/plain;charset=utf-8'});
    const url = URL.createObjectURL(blob); const a = document.createElement('a'); a.href = url; a.download = filename; document.body.appendChild(a); a.click();
    setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 1000);
    return true;
  } catch (e) { console.warn(e); return false; }
}
function tierBadge(w) { return '<span class="badge t' + w.tier + '">' + TIER_NAME[w.tier] + '</span>'; }
function testBadge(w) { return w.tests === 1 ? '<span class="badge test" title="Classic hard SAT-list word; less likely to matter on the ACT">SAT-only</span>' : ''; }
function statusBadge(w) { const s = statusOf(w); return '<span class="badge st-' + s + '">' + (s === 'new' ? 'Not started' : s) + '</span>'; }


/* ============================================================
   App layer: install, offline, updates, daily goal
   ============================================================ */
const isStandalone = () => window.matchMedia('(display-mode: standalone)').matches || window.navigator.standalone === true;
const isIOS = () => /iPad|iPhone|iPod/.test(navigator.userAgent) || (navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1);

let deferredPrompt = null;
let installEligible = false;

/* ---------- Daily goal ---------- */
function goalRender() {
  const el = $('#goalRing'); if (!el) return;
  const goal = Math.max(1, S().goal || 20);
  const done = todayCount();
  const pct = Math.min(1, done / goal);
  const R = 26, C = 2 * Math.PI * R;
  el.innerHTML = `<svg viewBox="0 0 64 64" aria-hidden="true"><circle class="track" cx="32" cy="32" r="${R}"></circle>
    <circle class="fill${pct >= 1 ? ' done' : ''}" cx="32" cy="32" r="${R}" stroke-dasharray="${C}" stroke-dashoffset="${C * (1 - pct)}"></circle></svg>
    <span class="goal-num">${done >= goal ? '✓' : done}</span>`;
  const lbl = $('#goalLabel');
  if (lbl) lbl.innerHTML = done >= goal
    ? `<b>Daily goal complete!</b> ${fmt(done)} reviews today — keep going if you're on a roll.`
    : `<b>${fmt(done)} of ${fmt(goal)}</b> reviews toward today's goal.`;
  const sel = $('#goalSel'); if (sel && sel.value !== String(goal)) sel.value = String(goal);
}

/* ---------- Install ---------- */
function showInstall(show) {
  installEligible = !!show;
  const b = $('#installBtn'); if (b) b.hidden = !show;
  const c = $('#installCard'); if (c) c.hidden = !show;
}
/* Flashcard sessions hide the card to keep the deck above the fold; put it back afterwards. */
function restoreInstallCard() { const c = $('#installCard'); if (c) c.hidden = !installEligible; }
function iosInstallModal() {
  openModal(`<h2>Add WordBank Prep to your Home Screen</h2>
    <p>iPhone and iPad install apps straight from Safari — it takes two taps and then the app works with no internet connection.</p>
    <ol>
      <li>Tap the <b>Share</b> button at the bottom of Safari (the square with an arrow pointing up).</li>
      <li>Scroll down and tap <b>Add to Home Screen</b>.</li>
      <li>Tap <b>Add</b>. WordBank Prep now has its own icon, opens full-screen, and works offline.</li>
    </ol>
    <p class="muted small">If you don't see Share, make sure you're in Safari rather than another browser or an in-app browser.</p>
    <div class="row" style="justify-content:flex-end;margin-top:16px"><button class="btn primary" data-close>Got it</button></div>`);
  S().iosHintSeen = true; save();
}
function initInstall() {
  window.addEventListener('beforeinstallprompt', e => {
    e.preventDefault(); deferredPrompt = e;
    if (!S().installDismissed) showInstall(true);
  });
  window.addEventListener('appinstalled', () => { deferredPrompt = null; showInstall(false); toast('Installed — look for WordBank on your home screen'); });
  const doInstall = async () => {
    if (deferredPrompt) {
      deferredPrompt.prompt();
      const res = await deferredPrompt.userChoice.catch(() => null);
      deferredPrompt = null;
      if (!res || res.outcome !== 'accepted') { S().installDismissed = true; save(); }
      showInstall(false);
    } else if (isIOS()) iosInstallModal();
    else openModal(`<h2>Install WordBank Prep</h2><p>In your browser's menu, look for <b>Install app</b> or <b>Add to Home Screen</b>. Once installed it opens full-screen and works with no internet connection.</p>
      <div class="row" style="justify-content:flex-end;margin-top:16px"><button class="btn primary" data-close>Got it</button></div>`);
  };
  $$('#installBtn, #installCardBtn').forEach(b => b && b.addEventListener('click', doInstall));
  const dismiss = $('#installDismiss');
  if (dismiss) dismiss.addEventListener('click', () => { S().installDismissed = true; save(); showInstall(false); });
  if (!isStandalone() && isIOS() && !S().installDismissed) showInstall(true);
}

/* ---------- Offline + updates ---------- */
function setOnline(on) {
  const b = $('#offlineBar'); if (b) b.hidden = on;
  document.documentElement.classList.toggle('is-offline', !on);
}
function initNetwork() {
  setOnline(navigator.onLine !== false);
  window.addEventListener('online', () => { setOnline(true); toast('Back online'); });
  window.addEventListener('offline', () => setOnline(false));
}
function initServiceWorker() {
  if (!('serviceWorker' in navigator)) return;
  window.addEventListener('load', () => {
    navigator.serviceWorker.register('sw.js').then(reg => {
      reg.addEventListener('updatefound', () => {
        const nw = reg.installing; if (!nw) return;
        nw.addEventListener('statechange', () => {
          if (nw.state === 'installed' && navigator.serviceWorker.controller) {
            const bar = $('#updateBar'); if (bar) bar.hidden = false;
            const btn = $('#updateBtn');
            if (btn) btn.onclick = () => { nw.postMessage({type: 'SKIP_WAITING'}); };
          }
        });
      });
    }).catch(e => console.warn('SW registration failed', e));
    let refreshing = false;
    navigator.serviceWorker.addEventListener('controllerchange', () => { if (refreshing) return; refreshing = true; location.reload(); });
  });
}

/* ---------- Keep the bottom nav on screen ----------
   `position:fixed; bottom:0` anchors to the LAYOUT viewport, which on iOS Safari
   (and any browser with dynamic toolbars) can sit below the visible area. Anchor
   it to the visual viewport instead, and get out of the way of the keyboard. */
function fitBottomNav() {
  const vv = window.visualViewport;
  const root = document.documentElement;
  if (!vv) { root.style.setProperty('--bnav-shift', '0px'); return; }
  const overhang = Math.max(0, Math.round(window.innerHeight - (vv.height + vv.offsetTop)));
  const keyboard = overhang > 140;                       // on-screen keyboard, not a toolbar
  root.classList.toggle('kb-open', keyboard);
  root.style.setProperty('--bnav-shift', (keyboard ? 0 : overhang) + 'px');
}
function initViewportFit() {
  fitBottomNav();
  // resize only: recomputing during scroll makes the bar bob as mobile toolbars collapse
  if (window.visualViewport) window.visualViewport.addEventListener('resize', fitBottomNav);
  window.addEventListener('resize', fitBottomNav);
  window.addEventListener('orientationchange', () => setTimeout(fitBottomNav, 150));
  setTimeout(fitBottomNav, 300);
}

/* ---------- Standalone niceties ---------- */
function initAppChrome() {
  if (isStandalone()) document.documentElement.classList.add('standalone');
  // keep the safe-area padding correct when the phone rotates
  window.addEventListener('orientationchange', () => setTimeout(() => window.scrollTo(0, 0), 120));
  const sel = $('#goalSel');
  if (sel) sel.addEventListener('change', e => { S().goal = +e.target.value; save(); goalRender(); });
}

function initApp() { initInstall(); initNetwork(); initAppChrome(); initViewportFit(); goalRender(); }


/* ============================================================
   Flashcards with spaced repetition
   ============================================================ */
const FC = {queue: [], idx: 0, session: null, flipped: false, undo: null, autoTimer: null, reinserts: new Map()};

function fcCounts() {
  const pool = filtered(); const now = Date.now();
  let due = 0, fresh = 0, missed = 0;
  for (const w of pool) { const c = state.cards[w.w]; if (!c || !c.s) fresh++; else { if (c.d <= now) due++; if (c.x > 0 && c.b < 3) missed++; } }
  return {pool: pool.length, due, fresh, missed};
}
function fcRenderInfo() {
  const c = fcCounts();
  $('#fcDeckInfo').innerHTML = `Selected words: <b>${fmt(c.pool)}</b> · Due for review now: <b>${fmt(c.due)}</b> · Not yet studied: <b>${fmt(c.fresh)}</b> · Missed: <b>${fmt(c.missed)}</b>`;
}
function fcBuildDeck() {
  const pool = filtered(); const mode = S().fcDeck; const size = S().fcSize; const now = Date.now();
  const due = [], fresh = [], missed = [];
  for (const w of pool) { const c = state.cards[w.w]; if (!c || !c.s) fresh.push(w); else { if (c.d <= now) due.push(w); if (c.x > 0 && c.b < 3) missed.push(w); } }
  due.sort((a, b) => state.cards[a.w].d - state.cards[b.w].d);
  const freshOrdered = shuffle(fresh).sort((a, b) => a.tier - b.tier);
  let deck;
  if (mode === 'smart') deck = due.concat(freshOrdered);
  else if (mode === 'new') deck = freshOrdered;
  else if (mode === 'due') deck = due;
  else if (mode === 'missed') deck = shuffle(missed);
  else deck = shuffle(pool);
  const n = size === 'all' ? deck.length : Math.min(deck.length, +size);
  return deck.slice(0, n);
}
function fcStart(deck) {
  FC.queue = deck; FC.idx = 0; FC.undo = null; FC.reinserts = new Map();
  FC.session = {start: Date.now(), again: 0, hard: 0, good: 0, missed: new Set(), seen: new Set()};
  $('#welcome').hidden = true; $('#fcSetup').hidden = true; $('#fcSummary').hidden = true; $('#fcStage').hidden = false;
  const gp = $('#goalPanel'); if (gp) gp.hidden = true;
  const ic = $('#installCard'); if (ic) ic.hidden = true;
  fcRenderCard();
  window.scrollTo({top: 0});
}
function fcFrontHtml(w) {
  const front = S().fcFront;
  const top = `<div class="topline">${tierBadge(w)}<span>${FC.idx + 1} of ${FC.queue.length}</span></div>`;
  if (front === 'def') return top + `<div class="def-front">${esc(w.def)}</div><div class="pos">${esc(w.pos)}</div><div class="hint">Which word is this? Tap or press Space to reveal</div>`;
  if (front === 'ex') { const b = blankSentence(w, '<span class="blank">&nbsp;</span>'); return top + `<div class="def-front">${b || esc(w.def)}</div><div class="pos">${esc(w.pos)}</div><div class="hint">Which word fits? Tap or press Space to reveal</div>`; }
  return top + `<div class="word">${esc(w.w)}</div><div class="pos">${esc(w.pos)}</div><div class="hint">Tap or press Space to reveal the meaning</div>`;
}
function fcBackHtml(w) {
  const c = card(w); const st = statusOf(w);
  return `<div class="topline">${tierBadge(w)} ${testBadge(w)}<span>${st === 'new' ? 'New word' : 'Box ' + c.b + ' · ' + st}</span></div>
    <div class="back-body">
    <div class="word small">${esc(w.w)} <span class="pos">${esc(w.pos)}</span></div>
    <div class="def">${esc(w.def)}</div>
    <div class="ex">${highlightWord(w)}</div>
    <div class="syn"><b>Synonyms:</b> ${esc(w.syn.join(', '))}</div>
    </div>`;
}
function fcRenderCard() {
  clearTimeout(FC.autoTimer);
  const w = FC.queue[FC.idx]; if (!w) return fcFinish();
  FC.flipped = false; $('#fcCard').classList.remove('flipped');
  $('#fcFrontFace').innerHTML = fcFrontHtml(w);
  $('#fcBackFace').innerHTML = fcBackHtml(w);
  $('#fcCounter').textContent = (FC.idx + 1) + ' / ' + FC.queue.length;
  $('#fcBar').style.width = (100 * FC.idx / FC.queue.length) + '%';
  const s = FC.session; $('#fcQueueInfo').textContent = `✓ ${s.good + s.hard} · ✗ ${s.again}`;
  $('#fcUndo').disabled = !FC.undo;
  if ($('#fcAuto').checked) FC.autoTimer = setTimeout(() => fcFlip(true), 3000);
}
function fcFlip(force) { FC.flipped = force === true ? true : !FC.flipped; $('#fcCard').classList.toggle('flipped', FC.flipped); }
function fcRate(rating) {
  const w = FC.queue[FC.idx]; if (!w) return;
  const prev = state.cards[w.w] ? Object.assign({}, state.cards[w.w]) : null;
  rateWord(w, rating);
  const s = FC.session; s.seen.add(w.w); s[rating]++;
  let insertedAt = -1;
  if (rating === 'again') {
    s.missed.add(w.w);
    const n = FC.reinserts.get(w.w) || 0;
    if (n < 2) { const remaining = FC.queue.length - FC.idx - 1; insertedAt = FC.idx + 1 + Math.min(remaining, 6 + (n === 0 ? 0 : 3)); FC.queue.splice(insertedAt, 0, w); FC.reinserts.set(w.w, n + 1); }
  }
  haptic(rating === 'again' ? [12, 40, 12] : 10);
  FC.undo = {idx: FC.idx, word: w.w, prev, insertedAt, rating};
  FC.idx++;
  fcRenderCard();
  if (document.activeElement && document.activeElement.classList.contains('rate')) document.activeElement.blur();
}
function fcUndo() {
  const u = FC.undo; if (!u) return;
  const w = BY_WORD.get(u.word);
  if (u.prev) state.cards[u.word] = u.prev; else delete state.cards[u.word];
  const k = todayKey(); if (state.days[k]) state.days[k] = Math.max(0, state.days[k] - 1);
  const s = FC.session; s[u.rating] = Math.max(0, s[u.rating] - 1); if (u.rating === 'again') { const n = FC.reinserts.get(u.word) || 0; if (n > 0) FC.reinserts.set(u.word, n - 1); if (n <= 1) s.missed.delete(u.word); }
  if (u.insertedAt >= 0) FC.queue.splice(u.insertedAt, 1);
  FC.idx = u.idx; FC.undo = null; save(); fcRenderCard();
}
function fcSkip() {
  if (FC.idx >= FC.queue.length - 1) { toast('This is the last card in the session'); return; }
  const [w] = FC.queue.splice(FC.idx, 1); FC.queue.push(w); FC.undo = null; fcRenderCard();
}
function fcFinish() {
  clearTimeout(FC.autoTimer);
  const s = FC.session; if (!s) return;
  const total = s.good + s.hard + s.again; const secs = Math.round((Date.now() - s.start) / 1000);
  $('#fcStage').hidden = true; $('#fcSummary').hidden = false;
  const gp = $('#goalPanel'); if (gp) gp.hidden = false;
  if (typeof restoreInstallCard === 'function') restoreInstallCard();
  window.scrollTo({top: 0});
  const acc = total ? Math.round(100 * (s.good + s.hard) / total) : 0;
  $('#fcSummaryLead').textContent = total ? `You reviewed ${fmt(s.seen.size)} words (${fmt(total)} ratings) in ${Math.floor(secs / 60)}m ${secs % 60}s.` : 'No cards were rated in this session.';
  $('#fcStats').innerHTML = `<div class="stat good"><b>${s.good}</b><span>Got it</span></div><div class="stat warn"><b>${s.hard}</b><span>Hard</span></div><div class="stat bad"><b>${s.again}</b><span>Missed</span></div><div class="stat"><b>${acc}%</b><span>Accuracy</span></div>`;
  const missed = Array.from(s.missed).map(k => BY_WORD.get(k)).filter(Boolean);
  $('#fcMissed').innerHTML = missed.length ? `<h3 style="margin:14px 0 4px">Words to keep working on (${missed.length})</h3><ul class="missed-list">` + missed.map(w => `<li><b>${esc(w.w)}</b> <span class="pos">${esc(w.pos)}</span> — ${esc(w.def)}</li>`).join('') + '</ul>' : '<p class="muted">You didn\'t miss any words — nice work!</p>';
  $('#fcReviewMissed').hidden = !missed.length;
  FC.session = null;
  if (typeof progressRender === 'function') progressRender();
}
function fcBackToSetup() {
  $('#fcStage').hidden = true; $('#fcSummary').hidden = true; $('#fcSetup').hidden = false;
  const gp = $('#goalPanel'); if (gp) gp.hidden = false;
  if (typeof restoreInstallCard === 'function') restoreInstallCard();
  fcRenderInfo(); goalRender();
}
function fcKey(e) {
  if (!$('#view-flashcards').classList.contains('active') || $('#fcStage').hidden) return;
  const tag = (e.target.tagName || '').toLowerCase(); if (tag === 'input' || tag === 'select' || tag === 'textarea') return;
  if (tag === 'button' && e.target.id !== 'fcCard' && (e.key === ' ' || e.key === 'Enter')) return; // let focused buttons act normally
  if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); fcFlip(); }
  else if (e.key === '1') fcRate('again');
  else if (e.key === '2') fcRate('hard');
  else if (e.key === '3') fcRate('good');
  else if (e.key === 'u' || e.key === 'U') fcUndo();
  else if (e.key === 's' || e.key === 'S' || e.key === 'ArrowRight') fcSkip();
}
/* ---------- Swipe-to-rate ----------
   Touch is handled with non-passive touch events (and preventDefault on a
   horizontal drag) because Chrome/Safari otherwise hand the gesture to the
   page scroller mid-swipe and fire pointercancel. Mouse uses pointer events. */
const SW = {on: false, id: null, x0: 0, y0: 0, dx: 0, dy: 0, t0: 0, moved: false, axis: null};
function fcInitGestures() {
  const card = $('#fcCard');
  const hint = $('#swipeHint');
  const THRESH = 90, FAST = 44;

  const tint = (dir, amt) => {
    if (!hint) return;
    hint.className = 'swipe-tint' + (dir ? ' ' + dir : '');
    hint.style.opacity = dir ? Math.min(1, amt) : 0;
    hint.textContent = dir === 'right' ? 'Got it' : dir === 'left' ? 'Missed it' : '';
  };
  const reset = animate => {
    card.style.transition = animate ? 'transform .22s cubic-bezier(.2,.7,.2,1)' : '';
    card.style.transform = '';
    tint(null, 0);
    if (animate) setTimeout(() => { card.style.transition = ''; }, 240);
  };
  const fly = dir => {
    card.style.transition = 'transform .2s ease-out, opacity .2s ease-out';
    card.style.transform = `translateX(${dir === 'right' ? '120%' : '-120%'}) rotate(${dir === 'right' ? 12 : -12}deg)`;
    card.style.opacity = '0.15';
    setTimeout(() => {
      card.style.transition = ''; card.style.transform = ''; card.style.opacity = '';
      tint(null, 0);
      fcRate(dir === 'right' ? 'good' : 'again');
    }, 170);
  };

  const begin = (x, y) => { SW.on = true; SW.x0 = x; SW.y0 = y; SW.dx = SW.dy = 0; SW.t0 = Date.now(); SW.moved = false; SW.axis = null; card.style.transition = ''; };
  const move = (x, y) => {
    if (!SW.on) return false;
    SW.dx = x - SW.x0; SW.dy = y - SW.y0;
    if (!SW.moved) { if (Math.hypot(SW.dx, SW.dy) < 8) return false; SW.moved = true; SW.axis = Math.abs(SW.dx) > Math.abs(SW.dy) ? 'x' : 'y'; }
    if (SW.axis !== 'x') return false;                       // vertical belongs to the page scroller
    card.style.transform = `translateX(${SW.dx}px) rotate(${SW.dx / 26}deg)`;
    tint(SW.dx > 24 ? 'right' : SW.dx < -24 ? 'left' : null, Math.abs(SW.dx) / 110);
    return true;
  };
  const done = () => {
    if (!SW.on) return;
    SW.on = false;
    const quick = Date.now() - SW.t0 < 300;
    if (!SW.moved) { reset(false); fcFlip(); return; }
    if (SW.axis === 'x' && (Math.abs(SW.dx) > THRESH || (quick && Math.abs(SW.dx) > FAST))) return fly(SW.dx > 0 ? 'right' : 'left');
    reset(true);
  };

  // --- touch ---
  card.addEventListener('touchstart', e => { if (e.touches.length !== 1) { SW.on = false; return; } const t = e.touches[0]; begin(t.clientX, t.clientY); }, {passive: true});
  card.addEventListener('touchmove', e => {
    if (!SW.on || e.touches.length !== 1) return;
    const t = e.touches[0];
    if (move(t.clientX, t.clientY) && e.cancelable) e.preventDefault();   // keep the gesture from becoming a scroll
  }, {passive: false});
  card.addEventListener('touchend', done, {passive: true});
  card.addEventListener('touchcancel', () => { SW.on = false; reset(true); }, {passive: true});

  // --- mouse / stylus ---
  card.addEventListener('pointerdown', e => {
    if (e.pointerType === 'touch' || (e.button !== undefined && e.button !== 0)) return;
    begin(e.clientX, e.clientY);
    try { card.setPointerCapture(e.pointerId); SW.id = e.pointerId; } catch (err) {}
  });
  card.addEventListener('pointermove', e => { if (e.pointerType === 'touch') return; move(e.clientX, e.clientY); });
  card.addEventListener('pointerup', e => { if (e.pointerType === 'touch') return; done(); });
  card.addEventListener('pointercancel', e => { if (e.pointerType === 'touch') return; SW.on = false; reset(true); });
  card.addEventListener('dragstart', e => e.preventDefault());
  card.addEventListener('contextmenu', e => { if (SW.moved) e.preventDefault(); });
}

function initFlashcards() {
  const s = S();
  $('#fcDeck').value = s.fcDeck; $('#fcSize').value = s.fcSize; $('#fcFront').value = s.fcFront;
  $('#fcDeck').addEventListener('change', e => { S().fcDeck = e.target.value; save(); });
  $('#fcSize').addEventListener('change', e => { S().fcSize = e.target.value; save(); });
  $('#fcFront').addEventListener('change', e => { S().fcFront = e.target.value; save(); });
  $('#fcStart').addEventListener('click', () => {
    const deck = fcBuildDeck();
    if (!deck.length) { const mode = S().fcDeck; toast(mode === 'due' ? 'Nothing is due right now — try "New words" or "Smart review".' : mode === 'missed' ? 'No missed words yet in this selection.' : mode === 'new' ? 'No new words left in this selection — great job!' : 'No words match the current filters.'); return; }
    S().welcomed = true; save(); fcStart(deck);
  });
  $$('.startcard').forEach(b => b.addEventListener('click', () => { const t = b.dataset.start; S().tiers = t.split('').map(Number); S().welcomed = true; filtersChanged(); const deck = fcBuildDeck(); if (deck.length) fcStart(deck); }));
  fcInitGestures();
  $('#fcCard').addEventListener('keydown', e => { if (e.key === ' ' || e.key === 'Enter') { e.preventDefault(); e.stopPropagation(); fcFlip(); } });
  $('#fcFlip').addEventListener('click', () => fcFlip());
  $('#rateAgain').addEventListener('click', () => fcRate('again'));
  $('#rateHard').addEventListener('click', () => fcRate('hard'));
  $('#rateGood').addEventListener('click', () => fcRate('good'));
  $('#fcUndo').addEventListener('click', fcUndo);
  $('#fcSkip').addEventListener('click', fcSkip);
  $('#fcEnd').addEventListener('click', fcFinish);
  $('#fcAgain').addEventListener('click', fcBackToSetup);
  $('#fcReviewMissed').addEventListener('click', () => { const missed = Array.from($$('#fcMissed .missed-list li b')).map(b => BY_WORD.get(b.textContent)).filter(Boolean); if (missed.length) fcStart(shuffle(missed)); });
  document.addEventListener('keydown', fcKey);
  onFilterChange(() => { if (!$('#fcSetup').hidden) fcRenderInfo(); });
  onShowView('flashcards', () => { if (!$('#fcSetup').hidden) fcRenderInfo(); });
  $('#welcome').hidden = !!s.welcomed;
  fcRenderInfo();
}


/* ============================================================
   Multiple-choice quiz
   ============================================================ */
const QZ = {qs: [], i: 0, score: 0, answered: false, missed: [], start: 0};

function poolFor(sel) {
  const pool = filtered();
  if (sel === 'studied') return pool.filter(w => { const c = state.cards[w.w]; return c && c.s; });
  if (sel === 'missed') return pool.filter(isMissed);
  return pool;
}
function relatedWords(a, b) {
  if (a === b) return true;
  const ka = a.key.slice(0, 4), kb = b.key.slice(0, 4);
  if (ka === kb) return true;
  if (a.syn.some(s => norm(s) === b.key) || b.syn.some(s => norm(s) === a.key)) return true;
  return false;
}
function distractors(target, n) {
  const out = []; const used = new Set([target.id]);
  const tryPool = (list, tierTol) => {
    for (let k = 0; k < 400 && out.length < n; k++) {
      const c = pickRandom(list); if (!c || used.has(c.id)) continue;
      if (Math.abs(c.tier - target.tier) > tierTol) continue;
      if (relatedWords(target, c)) continue;
      if (out.some(o => relatedWords(o, c) || o.def === c.def)) continue;
      used.add(c.id); out.push(c);
    }
  };
  tryPool(BY_POS[target.p], 0); tryPool(BY_POS[target.p], 1); tryPool(BY_POS[target.p], 3); tryPool(WORDS, 3);
  return out.slice(0, n);
}
function makeQuestion(target, type) {
  let t = type;
  if (t === 'mixed') { const r = RND(); t = r < 0.45 ? 'blank' : r < 0.75 ? 'd2w' : 'w2d'; }
  let prompt = null;
  if (t === 'blank') { prompt = blankSentence(target); if (!prompt) t = 'd2w'; }
  const ds = distractors(target, 3);
  const options = shuffle([target].concat(ds));
  const q = {type: t, target, options, correct: options.indexOf(target)};
  if (t === 'blank') { q.label = 'Fill in the blank'; q.prompt = `<div>${prompt}</div>`; q.render = o => `<span>${esc(o.w)}</span>`; }
  else if (t === 'd2w') { q.label = 'Which word matches this definition?'; q.prompt = `<div>${esc(target.def)} <span class="pos">(${esc(target.pos)})</span></div>`; q.render = o => `<span>${esc(o.w)}</span>`; }
  else { q.label = 'What does this word mean?'; q.prompt = `<div class="qword">${esc(target.w)}</div><div class="pos">${esc(target.pos)}</div>`; q.render = o => `<span>${esc(o.def)}</span>`; }
  return q;
}
function qRenderInfo() {
  const p = poolFor($('#qPool').value);
  $('#qInfo').innerHTML = `Words available for this quiz: <b>${fmt(p.length)}</b>` + (p.length < 4 ? ' — at least 4 words are needed.' : '');
}
function qStart(targets) {
  const type = S().qType;
  QZ.qs = targets.map(t => makeQuestion(t, type)); QZ.i = 0; QZ.score = 0; QZ.missed = []; QZ.start = Date.now();
  $('#qSetup').hidden = true; $('#qSummary').hidden = true; $('#qStage').hidden = false;
  qRenderQuestion();
}
function qRenderQuestion() {
  const q = QZ.qs[QZ.i]; if (!q) return qFinish();
  QZ.answered = false;
  $('#qProgress').textContent = `Question ${QZ.i + 1} of ${QZ.qs.length}`;
  $('#qScore').textContent = `Score: ${QZ.score}`;
  $('#qTypeLbl').textContent = q.label;
  $('#qPrompt').innerHTML = q.prompt;
  const wrap = $('#qOpts'); wrap.className = 'opts' + (q.type === 'w2d' ? '' : ' two'); wrap.innerHTML = '';
  q.options.forEach((o, i) => { const b = document.createElement('button'); b.className = 'opt-btn'; b.innerHTML = `<span class="key">${i + 1}</span>${q.render(o)}`; b.addEventListener('click', () => qAnswer(i)); wrap.appendChild(b); });
  $('#qFeedback').hidden = true; $('#qNext').hidden = true;
}
function qAnswer(i) {
  if (QZ.answered) return; QZ.answered = true;
  const q = QZ.qs[QZ.i]; const ok = i === q.correct;
  const btns = $$('#qOpts .opt-btn');
  btns.forEach((b, j) => { b.disabled = true; if (j === q.correct) b.classList.add('correct'); else if (j === i) b.classList.add('wrong'); });
  if (ok) QZ.score++; else QZ.missed.push(q.target);
  quizResult(q.target, ok);
  const t = q.target;
  const fb = $('#qFeedback'); fb.hidden = false; fb.className = 'feedback ' + (ok ? 'ok' : 'bad');
  fb.innerHTML = `<b>${ok ? 'Correct!' : 'Not quite.'}</b> ${ok ? '' : 'The answer is <b>' + esc(t.w) + '</b>.'}<div class="exp"><b>${esc(t.w)}</b> <i>${esc(t.pos)}</i> — ${esc(t.def)}<br><i>${highlightWord(t)}</i><br><span class="muted small">Synonyms: ${esc(t.syn.join(', '))}</span></div>`;
  $('#qScore').textContent = `Score: ${QZ.score}`;
  const nb = $('#qNext'); nb.hidden = false; nb.textContent = QZ.i + 1 >= QZ.qs.length ? 'See results' : 'Next'; nb.focus();
}
function qFinish() {
  const total = QZ.qs.length; const pct = total ? Math.round(100 * QZ.score / total) : 0; const secs = Math.round((Date.now() - QZ.start) / 1000);
  $('#qStage').hidden = true; $('#qSummary').hidden = false;
  $('#qBig').innerHTML = `${QZ.score}<small> / ${total} · ${pct}%</small>`;
  if (typeof chFinish === 'function' && chFinish(QZ.score, total, secs)) return;
  $('#qSummaryLead').textContent = (pct === 100 ? 'Perfect score! ' : pct >= 80 ? 'Strong work. ' : pct >= 60 ? 'Good progress — keep going. ' : 'Keep practicing — these words will stick. ') + `Completed in ${Math.floor(secs / 60)}m ${secs % 60}s.` + (QZ.missed.length ? ' Missed words are now flagged for review in Flashcards.' : '');
  $('#qMissedWrap').innerHTML = QZ.missed.length ? `<h3 style="margin:14px 0 4px">Words you missed (${QZ.missed.length})</h3><ul class="missed-list">` + QZ.missed.map(w => `<li><b>${esc(w.w)}</b> <span class="pos">${esc(w.pos)}</span> — ${esc(w.def)}<br><span class="muted small"><i>${highlightWord(w)}</i></span></li>`).join('') + '</ul>' : '';
  $('#qRetryMissed').hidden = !QZ.missed.length;
  if (typeof progressRender === 'function') progressRender();
}
function qKey(e) {
  if (!$('#view-quiz').classList.contains('active') || $('#qStage').hidden) return;
  const tag = (e.target.tagName || '').toLowerCase(); if (tag === 'input' || tag === 'select' || tag === 'textarea') return;
  if (['1', '2', '3', '4'].includes(e.key)) { const i = +e.key - 1; if (!QZ.answered && QZ.qs[QZ.i] && i < QZ.qs[QZ.i].options.length) qAnswer(i); }
  else if (e.key === 'Enter' && QZ.answered) { if (tag === 'button') return; e.preventDefault(); QZ.i++; qRenderQuestion(); }
}
function initQuiz() {
  $('#qType').value = S().qType; $('#qCount').value = S().qCount;
  $('#qType').addEventListener('change', e => { S().qType = e.target.value; save(); });
  $('#qCount').addEventListener('change', e => { S().qCount = e.target.value; save(); });
  $('#qPool').addEventListener('change', qRenderInfo);
  $('#qStart').addEventListener('click', () => {
    const pool = poolFor($('#qPool').value);
    if (pool.length < 4) { toast('Select at least 4 words for a quiz (adjust the filters or the "Words" option).'); return; }
    const weak = pool.filter(w => statusOf(w) !== 'mastered');
    const base = weak.length >= 4 ? weak : pool;
    const n = Math.min(+S().qCount, base.length);
    qStart(shuffle(base).slice(0, n));
  });
  $('#qNext').addEventListener('click', () => { QZ.i++; qRenderQuestion(); });
  $('#qQuit').addEventListener('click', () => { $('#qStage').hidden = true; $('#qSetup').hidden = false; qRenderInfo(); });
  $('#qRetryMissed').addEventListener('click', () => { if (QZ.missed.length) qStart(shuffle(QZ.missed)); });
  $('#qNew').addEventListener('click', () => { $('#qSummary').hidden = true; $('#qSetup').hidden = false; qRenderInfo(); });
  document.addEventListener('keydown', qKey);
  onFilterChange(() => { if (!$('#qSetup').hidden) qRenderInfo(); });
  onShowView('quiz', () => { if (!$('#qSetup').hidden) qRenderInfo(); });
  qRenderInfo();
}


/* ============================================================
   Head-to-head challenges — no server, no accounts.
   A challenge is a seed: both phones rebuild the identical quiz
   from it, so only a short link has to travel between students.
   ============================================================ */
const CH = {incoming: null, outgoing: null, active: null};
const CH_SEP = '.';

function chDataVersion() {
  const m = (typeof DATA_URL === 'string' ? DATA_URL : '').match(/words\.([0-9a-f]+)\.json/);
  return m ? m[1].slice(0, 6) : 'dev';
}
function chName(n) { return (n || '').replace(/[^\w '-]/g, '').trim().slice(0, 16); }

/* ---------- link encode / decode ---------- */
function chEncode(c) {
  return ['1', c.seed.toString(36), c.n, c.type, c.tiers.join(''), c.test, c.score, c.dv, encodeURIComponent(c.name || '')].join(CH_SEP);
}
function chDecode(str) {
  try {
    const p = String(str).split(CH_SEP);
    if (p[0] !== '1' || p.length < 8) return null;
    const c = {
      seed: parseInt(p[1], 36), n: Math.min(50, Math.max(1, parseInt(p[2], 10))), type: p[3],
      tiers: p[4].split('').map(Number).filter(t => t >= 1 && t <= 3),
      test: ['both', 'sat', 'act'].includes(p[5]) ? p[5] : 'both',
      score: Math.max(0, parseInt(p[6], 10)), dv: p[7], name: chName(decodeURIComponent(p.slice(8).join(CH_SEP) || ''))
    };
    if (!isFinite(c.seed) || !isFinite(c.n) || !isFinite(c.score) || !c.tiers.length) return null;
    if (!['mixed', 'blank', 'd2w', 'w2d'].includes(c.type)) c.type = 'mixed';
    if (c.score > c.n) return null;
    return c;
  } catch (e) { return null; }
}
function chUrl(c) {
  const base = location.origin + location.pathname.replace(/index\.html$/, '');
  return base + '#c=' + chEncode(c);
}

/* ---------- deterministic quiz ---------- */
/* Pool deliberately ignores per-student progress: both players must see the same words. */
function chPool(c) {
  const tiers = new Set(c.tiers);
  return WORDS.filter(w => tiers.has(w.tier) && !(c.test === 'act' && w.tests !== 0));
}
function chBuildQuestions(c) {
  const pool = chPool(c);
  if (pool.length < 8) return null;
  return withSeed(c.seed, () => {
    const targets = shuffle(pool).slice(0, Math.min(c.n, pool.length));
    return targets.map(t => makeQuestion(t, c.type));
  });
}

/* ---------- creating a challenge ---------- */
function chNewChallenge() {
  const s = S();
  const c = {
    seed: (Math.floor(Math.random() * 0xFFFFFFFF) >>> 0), n: Math.min(20, +s.qCount || 10),
    type: s.qType || 'mixed', tiers: s.tiers.slice().sort(), test: s.test, score: 0,
    dv: chDataVersion(), name: chName(s.nickname)
  };
  const qs = chBuildQuestions(c);
  if (!qs) { toast('Select at least 8 words in the filter bar to build a challenge.'); return; }
  CH.active = {mode: 'create', c};
  showView('quiz');
  QZ.qs = qs; QZ.i = 0; QZ.score = 0; QZ.missed = []; QZ.start = Date.now();
  $('#qSetup').hidden = true; $('#qSummary').hidden = true; $('#qStage').hidden = false;
  qRenderQuestion();
  toast('Set your score, then send the link');
}
function chAcceptIncoming() {
  const c = CH.incoming; if (!c) return;
  if (c.dv !== chDataVersion()) toast('Heads up: the word list has been updated since this challenge was made.');
  const qs = chBuildQuestions(c);
  if (!qs) { toast('This challenge link could not be opened.'); return; }
  CH.active = {mode: 'play', c};
  closeModal();
  showView('quiz');
  QZ.qs = qs; QZ.i = 0; QZ.score = 0; QZ.missed = []; QZ.start = Date.now();
  $('#qSetup').hidden = true; $('#qSummary').hidden = true; $('#qStage').hidden = false;
  qRenderQuestion();
}

/* ---------- finishing ---------- */
/* Returns true when it has taken over the summary screen. */
function chFinish(score, total, secs) {
  const a = CH.active; if (!a) return false;
  CH.active = null;
  const c = Object.assign({}, a.c, {score: a.mode === 'create' ? score : a.c.score});
  const wrap = $('#qMissedWrap');
  const missedHtml = QZ.missed.length
    ? `<h3 style="margin:16px 0 4px">Words you missed (${QZ.missed.length})</h3><ul class="missed-list">`
      + QZ.missed.map(w => `<li><b>${esc(w.w)}</b> <span class="pos">${esc(w.pos)}</span> — ${esc(w.def)}</li>`).join('') + '</ul>'
    : '';

  if (a.mode === 'create') {
    CH.outgoing = c;
    $('#qSummaryLead').textContent = `You scored ${score} out of ${total}. Now send the link — your friend gets these exact ${total} questions.`;
    wrap.innerHTML = `<div class="ch-box">
        <h3>Send your challenge</h3>
        <label class="opt ch-name">Your name (optional)
          <input class="inp" id="chNick" maxlength="16" placeholder="e.g. Cory" value="${esc(c.name || '')}">
        </label>
        <div class="row"><button class="btn primary" id="chShare">Share challenge link</button><button class="btn" id="chCopy">Copy link</button></div>
        <input class="inp ch-url" id="chUrl" readonly value="${esc(chUrl(c))}">
        <p class="small muted">The link carries only the question set and your score — no account, no personal data.</p>
      </div>` + missedHtml;
    const sync = () => { c.name = chName($('#chNick').value); CH.outgoing = c; $('#chUrl').value = chUrl(c); };
    $('#chNick').addEventListener('input', () => { sync(); S().nickname = c.name; save(); });
    $('#chShare').addEventListener('click', async () => {
      sync();
      const text = `${c.name ? c.name + ' scored' : 'I scored'} ${score}/${total} on this SAT & ACT vocab challenge. Beat it?`;
      if (navigator.share) { try { await navigator.share({title: 'WordBank Prep challenge', text, url: chUrl(c)}); return; } catch (e) { if (e && e.name === 'AbortError') return; } }
      chCopyLink();
    });
    $('#chCopy').addEventListener('click', () => { sync(); chCopyLink(); });
    $('#qRetryMissed').hidden = true; $('#qNew').textContent = 'Back to quizzes';
    return true;
  }

  // playing someone else's challenge
  const them = c.score, you = score;
  const verdict = you > them ? 'You win!' : you < them ? 'They win this one.' : "It's a tie!";
  const who = c.name || 'Your friend';
  $('#qBig').innerHTML = `${you}<small> / ${total}</small>`;
  $('#qSummaryLead').textContent = `${verdict} Completed in ${Math.floor(secs / 60)}m ${secs % 60}s.`;
  wrap.innerHTML = `<div class="ch-box">
      <div class="ch-vs">
        <div class="ch-side ${you >= them ? 'win' : ''}"><span>You</span><b>${you}</b></div>
        <div class="ch-mid">vs</div>
        <div class="ch-side ${them >= you ? 'win' : ''}"><span>${esc(who)}</span><b>${them}</b></div>
      </div>
      <div class="row"><button class="btn primary" id="chRematch">Send a rematch</button></div>
      <p class="small muted">A rematch builds a fresh set of questions and sends it back with your score.</p>
    </div>` + missedHtml;
  $('#chRematch').addEventListener('click', chNewChallenge);
  $('#qRetryMissed').hidden = !QZ.missed.length; $('#qNew').textContent = 'New quiz';
  return true;
}
function chCopyLink() {
  const url = $('#chUrl') ? $('#chUrl').value : (CH.outgoing ? chUrl(CH.outgoing) : '');
  const ok = () => toast('Link copied — paste it to a friend');
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(url).then(ok).catch(() => { const el = $('#chUrl'); if (el) { el.select(); document.execCommand && document.execCommand('copy'); ok(); } });
  } else { const el = $('#chUrl'); if (el) { el.select(); try { document.execCommand('copy'); ok(); } catch (e) { toast('Copy the link from the box above'); } } }
}

/* ---------- incoming link ---------- */
/* Accept the payload in the fragment (preferred — it never reaches a server log)
   or in a ?c= query, because some messaging apps strip fragments when they
   rewrite shared links. */
function chReadUrl() {
  const h = location.hash.match(/^#c=(.+)$/);
  if (h) return {raw: h[1], from: 'hash'};
  const q = new URLSearchParams(location.search).get('c');
  if (q) return {raw: q, from: 'query'};
  return null;
}
function chCheckUrl() {
  const found = chReadUrl();
  if (!found) return;
  const c = chDecode(decodeURIComponent(found.raw));
  const params = new URLSearchParams(location.search); params.delete('c');
  const qs = params.toString();
  history.replaceState(null, '', location.pathname + (qs ? '?' + qs : ''));
  if (!c) { toast('That challenge link is not valid.'); return; }
  CH.incoming = c;
  const who = c.name || 'A friend';
  const tierNames = c.tiers.map(t => TIER_NAME[t]).join(' + ');
  openModal(`<h2>${esc(who)} challenged you</h2>
    <p><b>${esc(who)}</b> scored <b>${c.score} out of ${c.n}</b>. You'll get the <b>exact same ${c.n} questions</b> — can you beat it?</p>
    <p class="muted small">${tierNames} words · ${c.type === 'blank' ? 'fill in the blank' : c.type === 'd2w' ? 'definition → word' : c.type === 'w2d' ? 'word → definition' : 'mixed question types'}</p>
    <div class="row" style="justify-content:flex-end;margin-top:16px"><button class="btn" data-close>Maybe later</button><button class="btn primary" id="chAccept">Accept challenge</button></div>`);
  $('#chAccept').addEventListener('click', chAcceptIncoming);
}
function initChallenge() {
  $$('#chStart, #chStartQuiz').forEach(b => b && b.addEventListener('click', chNewChallenge));
  chCheckUrl();
  window.addEventListener('hashchange', chCheckUrl);
}


/* ============================================================
   Matching game
   ============================================================ */
const MT = {pairs: [], selW: null, selD: null, matched: 0, mistakes: 0, timer: null, start: 0, done: false, wrongWords: new Set()};

function mRenderBest() {
  const best = state.match.best || {}; const keys = Object.keys(best).sort((a, b) => a - b);
  const pool = poolFor($('#mPool').value);
  $('#mBest').innerHTML = `Words available: <b>${fmt(pool.length)}</b>` + (keys.length ? ' · Best times: ' + keys.map(k => `${k} pairs — <b>${(best[k] / 1000).toFixed(1)}s</b>`).join(', ') : '');
}
function mPickPairs(pool, n) {
  const weak = pool.filter(w => statusOf(w) !== 'mastered'); const base = shuffle(weak.length >= n ? weak : pool);
  const chosen = [];
  for (const c of base) { if (chosen.length >= n) break; if (chosen.some(o => relatedWords(o, c) || o.def === c.def)) continue; chosen.push(c); }
  return chosen;
}
function mStart() {
  const pool = poolFor($('#mPool').value); const n = +S().mPairs;
  if (pool.length < n) { toast(`Select at least ${n} words (adjust the filters or the "Words" option).`); return; }
  MT.pairs = mPickPairs(pool, n); MT.selW = MT.selD = null; MT.matched = 0; MT.mistakes = 0; MT.done = false; MT.wrongWords = new Set();
  $('#mSetup').hidden = true; $('#mSummary').hidden = true; $('#mStage').hidden = false;
  $('#mTotal').textContent = MT.pairs.length; $('#mMatched').textContent = '0'; $('#mMistakes').textContent = '0';
  const wc = $('#mWords'), dc = $('#mDefs'); wc.innerHTML = ''; dc.innerHTML = '';
  shuffle(MT.pairs).forEach((w, i) => { const b = document.createElement('button'); b.className = 'tile wordtile'; b.dataset.id = w.id; b.style.gridRow = i + 1; b.textContent = w.w; b.addEventListener('click', () => mSelect('w', b)); wc.appendChild(b); });
  shuffle(MT.pairs).forEach((w, i) => { const b = document.createElement('button'); b.className = 'tile'; b.dataset.id = w.id; b.style.gridRow = i + 1; b.textContent = w.def; b.addEventListener('click', () => mSelect('d', b)); dc.appendChild(b); });
  MT.start = Date.now(); clearInterval(MT.timer); MT.timer = setInterval(() => { $('#mTimer').textContent = ((Date.now() - MT.start) / 1000).toFixed(1) + 's'; }, 100);
}
function mSelect(kind, btn) {
  if (MT.done || btn.classList.contains('done')) return;
  const key = kind === 'w' ? 'selW' : 'selD';
  if (MT[key] === btn) { btn.classList.remove('sel'); MT[key] = null; return; }
  if (MT[key]) MT[key].classList.remove('sel');
  MT[key] = btn; btn.classList.add('sel');
  if (MT.selW && MT.selD) {
    const a = MT.selW, b = MT.selD; MT.selW = MT.selD = null;
    if (a.dataset.id === b.dataset.id) {
      [a, b].forEach(x => { x.classList.remove('sel'); x.classList.add('done', 'pop'); x.disabled = true; });
      MT.matched++; $('#mMatched').textContent = MT.matched;
      if (MT.matched >= MT.pairs.length) mFinish();
    } else {
      MT.mistakes++; $('#mMistakes').textContent = MT.mistakes;
      MT.wrongWords.add(+a.dataset.id); MT.wrongWords.add(+b.dataset.id);
      [a, b].forEach(x => { x.classList.remove('sel'); x.classList.add('shake'); });
      setTimeout(() => [a, b].forEach(x => x.classList.remove('shake')), 400);
    }
  }
}
function mFinish() {
  MT.done = true; clearInterval(MT.timer);
  const ms = Date.now() - MT.start; const n = MT.pairs.length;
  const best = state.match.best || (state.match.best = {});
  const isBest = !best[n] || ms < best[n]; if (isBest) best[n] = ms;
  MT.pairs.forEach(w => { const c = ensureCard(w); c.s++; c.l = Date.now(); if (MT.wrongWords.has(w.id) && c.b < 3) { /* light penalty: mark as seen but not correct */ } });
  bumpDay(); save();
  $('#mStage').hidden = true; $('#mSummary').hidden = false;
  $('#mSummaryLead').textContent = `You matched ${n} pairs in ${(ms / 1000).toFixed(1)} seconds with ${MT.mistakes} mistake${MT.mistakes === 1 ? '' : 's'}.` + (isBest ? ' New best time for this size!' : ` Best: ${(best[n] / 1000).toFixed(1)}s.`);
  $('#mReview').innerHTML = '<ul class="missed-list">' + MT.pairs.map(w => `<li><b>${esc(w.w)}</b> <span class="pos">${esc(w.pos)}</span> — ${esc(w.def)}${MT.wrongWords.has(w.id) ? ' <span class="badge st-learning">missed once</span>' : ''}</li>`).join('') + '</ul>';
  if (typeof progressRender === 'function') progressRender();
}
function initMatch() {
  $('#mPairs').value = S().mPairs;
  $('#mPairs').addEventListener('change', e => { S().mPairs = e.target.value; save(); });
  $('#mPool').addEventListener('change', mRenderBest);
  $('#mStart').addEventListener('click', mStart);
  $('#mAgain').addEventListener('click', mStart);
  $('#mBack').addEventListener('click', () => { $('#mSummary').hidden = true; $('#mSetup').hidden = false; mRenderBest(); });
  $('#mQuit').addEventListener('click', () => { clearInterval(MT.timer); MT.done = true; $('#mStage').hidden = true; $('#mSetup').hidden = false; mRenderBest(); });
  onFilterChange(() => { if (!$('#mSetup').hidden) mRenderBest(); });
  onShowView('match', () => { if (!$('#mSetup').hidden) mRenderBest(); });
  mRenderBest();
}


/* ============================================================
   Word list: search, sort, browse, mark, export, print
   ============================================================ */
const LS = {page: 0, query: '', rows: [], expanded: new Set(), allExpanded: false};

function weakness(w) { const s = statusOf(w); if (isMissed(w)) return 0; return {learning: 1, new: 2, known: 3, mastered: 4}[s]; }
function listCompute() {
  let rows = filtered();
  const q = norm(LS.query.trim());
  if (q) {
    const scored = [];
    for (const w of rows) {
      let score = -1;
      if (w.key === q) score = 0; else if (w.key.startsWith(q)) score = 1; else if (w.key.includes(q)) score = 2;
      else if (norm(w.def).includes(q)) score = 3; else if (w.syn.some(s => norm(s).includes(q))) score = 4; else if (norm(w.ex).includes(q)) score = 5;
      if (score >= 0) scored.push([score, w]);
    }
    scored.sort((a, b) => a[0] - b[0] || a[1].key.localeCompare(b[1].key));
    rows = scored.map(x => x[1]);
  } else {
    const sort = $('#sortSel').value;
    if (sort === 'tier') rows = rows.slice().sort((a, b) => a.tier - b.tier || a.key.localeCompare(b.key));
    else if (sort === 'status') rows = rows.slice().sort((a, b) => weakness(a) - weakness(b) || a.key.localeCompare(b.key));
    else if (sort === 'recent') rows = rows.slice().sort((a, b) => ((card(b) || {}).l || 0) - ((card(a) || {}).l || 0) || a.key.localeCompare(b.key));
  }
  LS.rows = rows;
}
function markText(text, q) {
  if (!q) return esc(text);
  const nt = norm(text); const i = nt.indexOf(q);
  if (i < 0) return esc(text);
  return esc(text.slice(0, i)) + '<mark>' + esc(text.slice(i, i + q.length)) + '</mark>' + esc(text.slice(i + q.length));
}
function rowHtml(w, q) {
  const open = LS.allExpanded || LS.expanded.has(w.id);
  const st = statusOf(w);
  return `<div class="wrow" data-id="${w.id}">
    <button class="wrow-head" aria-expanded="${open}">
      <span class="w"><span class="status-dot ${st}" title="${st}"></span>${markText(w.w, q)}<span class="pos">${esc(w.pos)}</span></span>
      <span class="d">${markText(w.def, q)}</span>
      <span class="badges">${tierBadge(w)}${testBadge(w)}${st !== 'new' ? statusBadge(w) : ''}</span>
    </button>
    <div class="wrow-body" ${open ? '' : 'hidden'}>
      <div></div>
      <div>
        <p class="ex">${highlightWord(w)}</p>
        <div class="syn"><b>Synonyms:</b> ${esc(w.syn.join(', '))}</div>
        <div class="acts">
          <button class="btn sm" data-act="mastered">Mark as mastered</button>
          <button class="btn sm" data-act="review">Mark for review</button>
          ${card(w) ? '<button class="btn sm ghost" data-act="reset">Reset progress for this word</button>' : ''}
        </div>
      </div>
    </div>
  </div>`;
}
function listRender() {
  listCompute();
  const size = +$('#pageSize').value; const total = LS.rows.length; const pages = Math.max(1, Math.ceil(total / size));
  if (LS.page >= pages) LS.page = pages - 1; if (LS.page < 0) LS.page = 0;
  const start = LS.page * size; const slice = LS.rows.slice(start, start + size);
  const q = norm(LS.query.trim());
  $('#wordList').innerHTML = slice.length ? slice.map(w => rowHtml(w, q)).join('') : `<div class="empty"><h3>No words found</h3><p>Try a different search or loosen the filters in the bar above.</p></div>`;
  $('#listLead').textContent = total ? `Showing ${fmt(start + 1)}–${fmt(Math.min(total, start + size))} of ${fmt(total)} words${q ? ' matching "' + LS.query.trim() + '"' : ''}. Click a word to see its example sentence and synonyms.` : 'Browse, search, and mark words. Filters in the bar above apply here too.';
  const pg = $('#pager');
  pg.innerHTML = pages > 1 ? `<button class="btn sm" data-pg="prev" ${LS.page === 0 ? 'disabled' : ''}>← Prev</button><span>Page ${LS.page + 1} of ${pages}</span><button class="btn sm" data-pg="next" ${LS.page >= pages - 1 ? 'disabled' : ''}>Next →</button>` : '';
  $$('#pager [data-pg]').forEach(b => b.addEventListener('click', () => { LS.page += b.dataset.pg === 'next' ? 1 : -1; listRender(); $('#view-list').scrollIntoView({behavior: 'smooth'}); }));
  $('#expandAll').textContent = LS.allExpanded ? 'Collapse all' : 'Expand all';
}
function listClick(e) {
  const head = e.target.closest('.wrow-head');
  if (head) { const row = head.closest('.wrow'); const id = +row.dataset.id; const body = $('.wrow-body', row); const open = body.hidden; body.hidden = !open; head.setAttribute('aria-expanded', open); if (open) LS.expanded.add(id); else { LS.expanded.delete(id); if (LS.allExpanded) LS.allExpanded = false; } return; }
  const act = e.target.closest('[data-act]');
  if (act) {
    const row = act.closest('.wrow'); const w = WORDS[+row.dataset.id];
    if (act.dataset.act === 'mastered') { setMastered(w); toast(`"${w.w}" marked as mastered`); }
    else if (act.dataset.act === 'review') { setReview(w); toast(`"${w.w}" will come up for review`); }
    else { resetWord(w); toast(`Progress reset for "${w.w}"`); }
    LS.expanded.add(w.id);
    listRender(); renderFilterBar();
  }
}
function csvEscape(v) { v = String(v); return /[",\n]/.test(v) ? '"' + v.replace(/"/g, '""') + '"' : v; }
function exportCsv() {
  listCompute();
  const rows = LS.rows;
  const lines = [['Word', 'Part of speech', 'Tier', 'Tests', 'Definition', 'Example sentence', 'Synonyms', 'Your status'].join(',')];
  rows.forEach(w => lines.push([w.w, w.pos, TIER_NAME[w.tier], w.tests === 0 ? 'SAT & ACT' : 'SAT', w.def, w.ex, w.syn.join('; '), statusOf(w)].map(csvEscape).join(',')));
  const ok = download('wordbank-sat-act-vocabulary.csv', '\uFEFF' + lines.join('\n'), 'text/csv;charset=utf-8');
  toast(ok ? `Exported ${fmt(rows.length)} words to CSV` : 'Download blocked in this view — open the file in your browser to export.');
}
function printList() {
  listCompute();
  const rows = LS.rows;
  const html = `<!DOCTYPE html><html><head><meta charset="utf-8"><title>WordBank Prep — SAT &amp; ACT Vocabulary List</title>
  <style>body{font-family:Georgia,serif;margin:28px;color:#111}h1{font-size:20px;margin:0 0 4px}p.sub{margin:0 0 16px;color:#555;font-size:12px;font-family:system-ui,sans-serif}
  .e{page-break-inside:avoid;padding:6px 0;border-bottom:1px solid #ddd;font-size:12.5px;line-height:1.35}.w{font-weight:700;font-size:14px}.p{font-style:italic;color:#555}.t{font-family:system-ui,sans-serif;font-size:9px;text-transform:uppercase;letter-spacing:.05em;color:#555;margin-left:6px;border:1px solid #bbb;border-radius:8px;padding:0 5px}
  .x{color:#444;font-style:italic}.s{color:#555;font-size:11.5px;font-family:system-ui,sans-serif}@media print{body{margin:0.4in}}</style></head><body>
  <h1>WordBank Prep — SAT &amp; ACT Vocabulary List</h1><p class="sub">${fmt(rows.length)} words${LS.query.trim() ? ' matching "' + esc(LS.query.trim()) + '"' : ''} · Tiers: Core = highest priority, Extended = standard prep lists, Advanced = for top scorers</p>
  ${rows.map(w => `<div class="e"><span class="w">${esc(w.w)}</span> <span class="p">${esc(w.pos)}</span><span class="t">${TIER_NAME[w.tier]}</span>${w.tests === 1 ? '<span class="t">SAT-only</span>' : ''}<br>${esc(w.def)}<br><span class="x">${esc(w.ex)}</span><br><span class="s">Synonyms: ${esc(w.syn.join(', '))}</span></div>`).join('')}
  <script>window.onload=function(){setTimeout(function(){window.print()},300)}<\/script></body></html>`;
  let win = null;
  try { win = window.open('', '_blank'); } catch (e) { win = null; }
  if (win && win.document) { win.document.open(); win.document.write(html); win.document.close(); }
  else { const ok = download('wordbank-vocabulary-print.html', html, 'text/html;charset=utf-8'); toast(ok ? 'Pop-ups are blocked — a printable HTML file was downloaded instead.' : 'Printing is not available in this view. Open the file in your browser to print.'); }
}
let searchTimer = null;
function initList() {
  $('#searchBox').addEventListener('input', e => { clearTimeout(searchTimer); searchTimer = setTimeout(() => { LS.query = e.target.value; LS.page = 0; listRender(); }, 140); });
  $('#sortSel').addEventListener('change', () => { LS.page = 0; listRender(); });
  $('#pageSize').addEventListener('change', () => { LS.page = 0; listRender(); });
  $('#expandAll').addEventListener('click', () => { LS.allExpanded = !LS.allExpanded; if (!LS.allExpanded) LS.expanded.clear(); listRender(); });
  $('#wordList').addEventListener('click', listClick);
  $('#exportCsv').addEventListener('click', exportCsv);
  $('#printList').addEventListener('click', printList);
  onFilterChange(() => { LS.page = 0; if ($('#view-list').classList.contains('active')) listRender(); });
  onShowView('list', listRender);
}


/* ============================================================
   Progress dashboard, backup / restore, reset
   ============================================================ */
function streakInfo() {
  const days = state.days || {}; const today = todayKey();
  let count = 0; const d = new Date();
  if (!days[today]) d.setDate(d.getDate() - 1); // streak may still be alive from yesterday
  while (days[todayKey(d)]) { count++; d.setDate(d.getDate() - 1); }
  return {count, today: days[today] || 0, active: !!days[today]};
}
function progressRender() {
  if (typeof goalRender === 'function') goalRender();
  const now = Date.now();
  const tally = {new: 0, learning: 0, known: 0, mastered: 0}; let due = 0; let missed = 0;
  const byTier = {1: {new: 0, learning: 0, known: 0, mastered: 0}, 2: {new: 0, learning: 0, known: 0, mastered: 0}, 3: {new: 0, learning: 0, known: 0, mastered: 0}};
  for (const w of WORDS) { const s = statusOf(w); tally[s]++; byTier[w.tier][s]++; if (isDue(w, now) && s !== 'new') due++; if (isMissed(w)) missed++; }
  const studied = WORDS.length - tally.new;
  $('#storageNote').innerHTML = storageOK ? 'Saved automatically on this device — no account needed.' : '<b>Heads up:</b> this browser is blocking storage (private mode?), so progress will reset when you close the page.';
  $('#pgCards').innerHTML = `
    <div class="stat"><b>${fmt(WORDS.length)}</b><span>Total words</span></div>
    <div class="stat"><b>${fmt(studied)}</b><span>Studied</span></div>
    <div class="stat warn"><b>${fmt(tally.learning)}</b><span>Learning</span></div>
    <div class="stat"><b style="color:var(--tier2)">${fmt(tally.known)}</b><span>Known</span></div>
    <div class="stat good"><b>${fmt(tally.mastered)}</b><span>Mastered</span></div>
    <div class="stat"><b style="color:var(--primary)">${fmt(due)}</b><span>Due for review</span></div>
    <div class="stat bad"><b>${fmt(missed)}</b><span>Needs work</span></div>`;
  $('#pgTiers').innerHTML = [1, 2, 3].map(t => { const c = byTier[t]; const total = c.new + c.learning + c.known + c.mastered; const pct = k => (100 * c[k] / total).toFixed(2) + '%';
    return `<div class="tierbar"><div class="lbl"><span><span class="badge t${t}">${TIER_NAME[t]}</span> ${fmt(total)} words</span><span class="muted">${fmt(c.mastered)} mastered · ${fmt(c.known)} known · ${fmt(c.learning)} learning · ${fmt(c.new)} not started</span></div>
    <div class="bar"><i class="c-mastered" style="width:${pct('mastered')}"></i><i class="c-known" style="width:${pct('known')}"></i><i class="c-learning" style="width:${pct('learning')}"></i><i class="c-new" style="width:${pct('new')}"></i></div></div>`; }).join('');
  const st = streakInfo();
  $('#pgStreak').innerHTML = `🔥 <b>${st.count}</b> day streak${st.active ? '' : (st.count ? ' — study today to keep it going!' : '')} · <b style="font-size:inherit">${fmt(st.today)}</b> reviews today`;
  const q = state.quiz || {attempts: 0, correct: 0}; const acc = q.attempts ? Math.round(100 * q.correct / q.attempts) : null;
  const best = state.match.best || {}; const bk = Object.keys(best).sort((a, b) => a - b);
  $('#pgQuiz').innerHTML = `Quiz questions answered: <b>${fmt(q.attempts)}</b>${acc !== null ? ` · accuracy <b>${acc}%</b>` : ''}` + (bk.length ? `<br>Best matching times: ${bk.map(k => k + ' pairs — <b>' + (best[k] / 1000).toFixed(1) + 's</b>').join(', ')}` : '');
  const coreLeft = byTier[1].new; const extLeft = byTier[2].new;
  const perDay = 20;
  $('#pgPlan').innerHTML = coreLeft > 0
    ? `<b>Suggested plan:</b> ${fmt(coreLeft)} Core words are not started yet. At ${perDay} new words a day plus your due reviews, you'll get through Core in about <b>${Math.ceil(coreLeft / perDay)} days</b>. Then move on to Extended (${fmt(extLeft)} remaining).`
    : extLeft > 0 ? `<b>Nice — every Core word has been started.</b> ${fmt(extLeft)} Extended words remain; at ${perDay} a day that's about <b>${Math.ceil(extLeft / perDay)} days</b>. Keep clearing your due reviews to move words to Mastered.`
    : `<b>Outstanding!</b> You've started every Core and Extended word. Keep reviewing due words and explore the Advanced tier for the toughest vocabulary.`;
}
function exportProgress() {
  const ok = download('wordbank-progress-backup.json', JSON.stringify(state), 'application/json');
  toast(ok ? 'Backup downloaded' : 'Download blocked in this view.');
}
function importProgress(file) {
  const reader = new FileReader();
  reader.onload = () => {
    try {
      const s = JSON.parse(reader.result);
      if (!s || typeof s !== 'object' || !s.cards) throw new Error('bad');
      confirmModal('Restore backup?', `This will replace your current progress with the backup (${fmt(Object.keys(s.cards).length)} studied words). This cannot be undone.`, 'Restore', () => {
        state = s; state.settings = Object.assign({}, DEFAULT_SETTINGS, s.settings || {}); state.quiz = s.quiz || {attempts: 0, correct: 0}; state.match = s.match || {best: {}}; state.days = s.days || {};
        save(); applyTheme(); renderFilterBar(); progressRender(); filterListeners.forEach(fn => fn()); toast('Progress restored');
      });
    } catch (e) { toast('That file is not a valid backup.'); }
  };
  reader.readAsText(file);
}
function initProgress() {
  goalRender();
  $('#exportProgress').addEventListener('click', exportProgress);
  $('#importProgress').addEventListener('change', e => { const f = e.target.files[0]; if (f) importProgress(f); e.target.value = ''; });
  $('#resetProgress').addEventListener('click', () => confirmModal('Reset all progress?', 'Every word will go back to "not started" and your quiz and matching stats will be cleared. Consider backing up first.', 'Reset everything', () => { state.cards = {}; state.quiz = {attempts: 0, correct: 0}; state.match = {best: {}}; state.days = {}; save(); renderFilterBar(); progressRender(); filterListeners.forEach(fn => fn()); toast('Progress reset'); }, true));
  onShowView('progress', progressRender);
}

/* ---------- Boot ---------- */
const DATA_URL = 'words.43e7b2491f.json';
function domReady() {
  return document.readyState === 'loading'
    ? new Promise(r => document.addEventListener('DOMContentLoaded', r))
    : Promise.resolve();
}
function bootError(msg) {
  const s = document.getElementById('splash');
  if (!s) return;
  s.innerHTML = '<div class="splash-inner"><div class="splash-logo">Wb</div>'
    + '<h1>WordBank Prep</h1><p class="splash-err">' + msg + '</p>'
    + '<button class="btn primary" onclick="location.reload()">Try again</button></div>';
}
async function boot() {
  await domReady();
  applyTheme();
  initServiceWorker();
  let raw;
  try {
    const res = await fetch(DATA_URL, {cache: 'force-cache'});
    if (!res.ok) throw new Error('HTTP ' + res.status);
    raw = await res.json();
    if (!Array.isArray(raw) || !raw.length) throw new Error('empty word list');
  } catch (e) {
    console.error('Could not load the word list', e);
    bootError(navigator.onLine === false
      ? 'The word list has not been saved to this device yet. Reconnect to the internet once and it will work offline from then on.'
      : 'Could not load the word list. Check your connection and try again.');
    return;
  }
  initData(raw);
  initShell(); initFilterBar(); initFlashcards(); initQuiz(); initMatch(); initList(); initProgress(); initApp(); initChallenge();
  progressRender();
  showView(S().view && $('#view-' + S().view) ? S().view : 'flashcards');
  const splash = document.getElementById('splash');
  if (splash) { splash.classList.add('gone'); setTimeout(() => splash.remove(), 320); }
  document.body.classList.add('ready');
}
boot();
