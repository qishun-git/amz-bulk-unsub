// ==UserScript==
// @name         Amazon Subscribe & Save Bulk Unsubscribe
// @namespace    local.amazon.bulk.unsubscribe
// @version      0.2.7
// @description  Bulk unsubscribe subscriptions on Amazon (supports manager page by redirecting to subscription list).
// @match        https://www.amazon.com/auto-deliveries/subscriptionList*
// @match        https://www.amazon.com/auto-deliveries/viewsubscriptions*
// @match        https://www.amazon.com/gp/subscribe-and-save/manager/viewsubscriptions*
// @match        https://www.amazon.com/fmc/*
// @run-at       document-idle
// @grant        none
// ==/UserScript==

(function () {
  'use strict';

  if (window.__amzBulkUnsubLoaded) return;
  window.__amzBulkUnsubLoaded = true;

  const CONFIG = {
    clickableSelector:
      'button, a, [role="button"], input[type="button"], input[type="submit"], input.a-button-input, span.a-button, span.a-button-text, span.a-button-inner',
    clickTargetSelector:
      'button, a, [role="button"], input[type="button"], input[type="submit"], input.a-button-input, span.a-button',
    editPatterns: [/^\s*edit\s*$/i, /^\s*edit\s*,/i],
    editExcludePatterns: [/^\s*edit subscriptions?\s*$/i, /^\s*manage subscriptions?\s*$/i],
    cancelStep1Patterns: [
      /\bcancel\b.*\b(subscription|auto[-\s]?delivery|delivery)\b/i,
      /\bend\b.*\bsubscription\b/i,
      /\bunsubscribe\b/i
    ],
    cancelStep2Patterns: [
      /\bcancel my subscription\b/i,
      /\bconfirm\b.*\b(cancel|cancellation|end|unsubscribe)\b/i,
      /\byes\b.*\b(cancel|cancellation|end|unsubscribe)\b/i,
      /\bcancel\b.*\b(subscription|auto[-\s]?delivery|delivery)\b/i,
      /\bend\b.*\bsubscription\b/i
    ],
    waitTimeoutMs: 45000,
    pollMs: 300,
    clickPauseMs: 900,
    betweenItemsPauseMs: 1400,
    resumeFindTimeoutMs: 22000,
    resumePollMs: 700,
    observerRefreshMs: 5000,
    scrollNudgeMs: 4000,
    redirectedPageLockMs: 1200,
    maxLogLines: 14
  };

  const PATHS = {
    managerView: /\/gp\/subscribe-and-save\/manager\/viewsubscriptions/i,
    subscriptionList: /\/auto-deliveries\/(subscriptionList|viewsubscriptions)/i
  };

  const MANAGER_REDIRECT_GUARD_KEY = '__amzBulkUnsubManagerRedirectAt';
  const RESUME_REDIRECT_GUARD_KEY = '__amzBulkUnsubResumeRedirectAt';
  const COMPLETION_RETURN_KEY = '__amzBulkUnsubCompletionReturnV1';
  const COMPLETION_REDIRECT_GUARD_KEY = '__amzBulkUnsubCompletionRedirectAt';
  const CANCEL_LANDING_REDIRECT_GUARD_KEY = '__amzBulkUnsubCancelLandingRedirectAt';
  const LAST_SUBSCRIPTION_URL_KEY = '__amzBulkUnsubLastSubscriptionUrlV1';
  const RUN_LOCK_KEY = '__amzBulkUnsubRunLockV1';
  const BULK_JOB_STORAGE_KEY = '__amzBulkUnsubJobV1';
  const BULK_JOB_VERSION = 1;

  const STATE = {
    subscriptions: [],
    selectedIds: new Set(),
    running: false,
    stopRequested: false,
    suppressObserver: false,
    refreshTimer: null,
    observer: null,
    panel: null,
    countEl: null,
    statusEl: null,
    runBtn: null,
    stopBtn: null,
    lockEl: null,
    keyboardGuardBound: false,
    pointerGuardBound: false,
    logEl: null,
    logLines: []
  };

  function log(message, level = 'info') {
    const prefix = '[AMZ bulk unsubscribe]';
    const line = `${new Date().toLocaleTimeString()} ${message}`;
    if (level === 'error') {
      console.error(prefix, message);
    } else {
      console.log(prefix, message);
    }
    STATE.logLines.push(line);
    if (STATE.logLines.length > CONFIG.maxLogLines) {
      STATE.logLines.splice(0, STATE.logLines.length - CONFIG.maxLogLines);
    }
    if (STATE.logEl) {
      STATE.logEl.textContent = STATE.logLines.join('\n');
      STATE.logEl.scrollTop = STATE.logEl.scrollHeight;
    }
  }

  function sleep(ms) {
    return new Promise((resolve) => setTimeout(resolve, ms));
  }

  function waitFor(getValue, timeoutMs, pollMs = CONFIG.pollMs) {
    return new Promise((resolve) => {
      const start = Date.now();
      const tick = () => {
        const value = getValue();
        if (value) return resolve(value);
        if (Date.now() - start >= timeoutMs) return resolve(null);
        setTimeout(tick, pollMs);
      };
      tick();
    });
  }

  function normalizeText(text) {
    return (text || '').replace(/\s+/g, ' ').trim();
  }

  function escapeHtml(text) {
    return String(text || '').replace(/[&<>"']/g, (ch) => {
      const map = {
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        '"': '&quot;',
        "'": '&#39;'
      };
      return map[ch] || ch;
    });
  }

  function getElementText(el) {
    if (!el) return '';
    const fromValue = el.value ? String(el.value) : '';
    const fromLabel = el.getAttribute('aria-label') || '';
    const fromInner = el.innerText || el.textContent || '';
    return normalizeText(`${fromInner} ${fromValue} ${fromLabel}`);
  }

  function isVisible(el) {
    if (!el || !(el instanceof Element)) return false;
    const style = window.getComputedStyle(el);
    if (style.visibility === 'hidden' || style.display === 'none') return false;
    const rect = el.getBoundingClientRect();
    return rect.width > 0 && rect.height > 0;
  }

  function isDisabled(el) {
    if (!el) return true;
    if (el.disabled) return true;
    if (el.getAttribute('aria-disabled') === 'true') return true;
    return false;
  }

  function textMatchesAny(text, regexes) {
    return regexes.some((re) => re.test(text));
  }

  function isManagerViewPage() {
    return PATHS.managerView.test(location.pathname);
  }

  function isSubscriptionListPage() {
    return PATHS.subscriptionList.test(location.pathname);
  }

  function normalizeUrl(url) {
    try {
      const parsed = new URL(url, location.origin);
      parsed.hash = '';
      return parsed.toString();
    } catch {
      return String(url || '');
    }
  }

  function extractShipIdFromUrl(url) {
    try {
      const parsed = new URL(url, location.origin);
      return normalizeText(parsed.searchParams.get('shipId') || '');
    } catch {
      return '';
    }
  }

  function buildSubscriptionListUrl(shipId = '') {
    const fallback = new URL('/auto-deliveries/subscriptionList', location.origin);
    const cleanShipId = normalizeText(shipId || '');
    if (cleanShipId) fallback.searchParams.set('shipId', cleanShipId);
    return fallback.toString();
  }

  function isFmcCancelResultPage() {
    if (!/^\/fmc\//i.test(location.pathname)) return false;
    try {
      const parsed = new URL(location.href);
      return normalizeText(parsed.searchParams.get('snsActionCompleted') || '').toLowerCase() === 'cancelsubscription';
    } catch {
      return false;
    }
  }

  function writeLastSubscriptionListUrl(targetUrl) {
    const normalized = normalizeUrl(targetUrl || '');
    if (!normalized) return;
    let parsed;
    try {
      parsed = new URL(normalized, location.origin);
    } catch {
      return;
    }
    if (!PATHS.subscriptionList.test(parsed.pathname)) return;
    try {
      sessionStorage.setItem(
        LAST_SUBSCRIPTION_URL_KEY,
        JSON.stringify({
          url: normalized,
          createdAt: Date.now()
        })
      );
    } catch {
      // Ignore storage write errors.
    }
  }

  function readLastSubscriptionListUrl() {
    try {
      const raw = sessionStorage.getItem(LAST_SUBSCRIPTION_URL_KEY);
      if (!raw) return '';
      const parsed = JSON.parse(raw);
      const url = normalizeText(parsed && parsed.url ? parsed.url : '');
      const createdAt = Number(parsed && parsed.createdAt ? parsed.createdAt : 0);
      if (!url) return '';
      if (!Number.isFinite(createdAt) || Date.now() - createdAt > 24 * 60 * 60 * 1000) {
        sessionStorage.removeItem(LAST_SUBSCRIPTION_URL_KEY);
        return '';
      }
      const normalized = normalizeUrl(url);
      if (!PATHS.subscriptionList.test(new URL(normalized).pathname)) return '';
      return normalized;
    } catch {
      return '';
    }
  }

  function shouldThrottleRedirect(guardKey, targetUrl, windowMs = 7000) {
    const target = normalizeUrl(targetUrl || '');
    const source = normalizeUrl(location.href);
    const now = Date.now();

    try {
      const raw = sessionStorage.getItem(guardKey);
      if (raw) {
        try {
          const parsed = JSON.parse(raw);
          const prevAt = Number(parsed && parsed.at ? parsed.at : 0);
          const prevSource = normalizeText(parsed && parsed.source ? parsed.source : '');
          const prevTarget = normalizeText(parsed && parsed.target ? parsed.target : '');
          if (
            Number.isFinite(prevAt) &&
            now - prevAt < windowMs &&
            prevSource === source &&
            prevTarget === target
          ) {
            return true;
          }
        } catch {
          const prevAt = Number(raw || '0');
          if (Number.isFinite(prevAt) && now - prevAt < windowMs) return true;
        }
      }

      sessionStorage.setItem(
        guardKey,
        JSON.stringify({
          at: now,
          source,
          target
        })
      );
    } catch {
      // Ignore storage issues and proceed with redirect.
    }

    return false;
  }

  function redirectWithLockDelay(targetUrl, delayMs = CONFIG.redirectedPageLockMs) {
    const target = normalizeUrl(targetUrl || '');
    if (!target) return false;
    const delay = Math.max(0, Number(delayMs) || 0);
    if (delay === 0) {
      location.assign(target);
      return true;
    }

    setTimeout(() => {
      location.assign(target);
    }, delay);
    return true;
  }

  function findSubscriptionListUrl() {
    const links = Array.from(document.querySelectorAll('a[href]'))
      .map((a) => a.getAttribute('href'))
      .filter(Boolean)
      .map((href) => {
        try {
          return new URL(href, location.origin);
        } catch {
          return null;
        }
      })
      .filter(Boolean);

    const direct = links.find((url) => PATHS.subscriptionList.test(url.pathname));
    if (direct) return direct.toString();

    let shipId = '';
    for (const url of links) {
      if (!/\/auto-deliveries\//i.test(url.pathname)) continue;
      const id = url.searchParams.get('shipId');
      if (id) {
        shipId = id;
        break;
      }
    }

    return buildSubscriptionListUrl(shipId);
  }

  function maybeRedirectFromManagerPage() {
    if (!isManagerViewPage()) return false;

    const target = findSubscriptionListUrl();
    if (!target) return false;

    if (normalizeUrl(target) === normalizeUrl(location.href)) return false;
    if (shouldThrottleRedirect(MANAGER_REDIRECT_GUARD_KEY, target)) return false;

    location.assign(target);
    return true;
  }

  function normalizeJobEntry(entry) {
    if (!entry || typeof entry !== 'object') return null;
    const id = normalizeText(entry.id || '');
    const title = normalizeText(entry.title || '');
    if (!id && !title) return null;
    return {
      id,
      title: title || 'Subscription item'
    };
  }

  function entriesMatch(a, b) {
    if (!a || !b) return false;
    if (a.id && b.id) return a.id === b.id;
    return normalizeText(a.title).toLowerCase() === normalizeText(b.title).toLowerCase();
  }

  function readStoredJob() {
    try {
      const raw = sessionStorage.getItem(BULK_JOB_STORAGE_KEY);
      if (!raw) return null;
      const parsed = JSON.parse(raw);
      if (!parsed || parsed.version !== BULK_JOB_VERSION) return null;
      if (!Array.isArray(parsed.pending)) return null;

      const pending = parsed.pending.map(normalizeJobEntry).filter(Boolean);
      const done = (Array.isArray(parsed.done) ? parsed.done : []).map(normalizeJobEntry).filter(Boolean);
      const failed = Array.isArray(parsed.failed) ? parsed.failed : [];
      const inFlight = normalizeJobEntry(parsed.inFlight);
      const resumeUrl = normalizeText(parsed.resumeUrl || '');

      return {
        version: BULK_JOB_VERSION,
        createdAt: Number(parsed.createdAt) || Date.now(),
        pending,
        done,
        failed,
        inFlight,
        resumeUrl
      };
    } catch {
      return null;
    }
  }

  function hasActiveStoredJob() {
    const job = readStoredJob();
    if (!job) return false;
    const pending = Array.isArray(job.pending) ? job.pending.length : 0;
    return pending > 0;
  }

  function writeStoredJob(job) {
    if (!job) return;
    try {
      sessionStorage.setItem(BULK_JOB_STORAGE_KEY, JSON.stringify(job));
    } catch {
      // Ignore storage write errors.
    }
  }

  function clearStoredJob() {
    try {
      sessionStorage.removeItem(BULK_JOB_STORAGE_KEY);
    } catch {
      // Ignore storage errors.
    }
  }

  function createStoredJob(targets) {
    return {
      version: BULK_JOB_VERSION,
      createdAt: Date.now(),
      pending: targets.map((item) => normalizeJobEntry({ id: item.id, title: item.title })).filter(Boolean),
      done: [],
      failed: [],
      inFlight: null,
      resumeUrl: normalizeUrl(location.href)
    };
  }

  function getJobResumeUrl(job) {
    const candidate = normalizeText(job && job.resumeUrl ? job.resumeUrl : '');
    if (candidate) {
      try {
        const parsed = new URL(candidate, location.origin);
        if (parsed.origin === location.origin && PATHS.subscriptionList.test(parsed.pathname)) {
          parsed.hash = '';
          return parsed.toString();
        }
      } catch {
        // Ignore invalid stored URL.
      }
    }

    const remembered = readLastSubscriptionListUrl();
    if (remembered) return remembered;

    return buildSubscriptionListUrl(extractShipIdFromUrl(location.href));
  }

  function maybeRedirectForPendingJob() {
    const job = readStoredJob();
    if (!job || !Array.isArray(job.pending) || job.pending.length === 0) return false;
    if (isSubscriptionListPage()) return false;

    const target = getJobResumeUrl(job);
    if (!target) return false;
    if (normalizeUrl(target) === normalizeUrl(location.href)) return false;
    if (shouldThrottleRedirect(RESUME_REDIRECT_GUARD_KEY, target)) return false;

    return redirectWithLockDelay(target);
  }

  function writeCompletionReturnUrl(targetUrl) {
    const normalized = normalizeUrl(targetUrl || '');
    if (!normalized) return;
    try {
      sessionStorage.setItem(
        COMPLETION_RETURN_KEY,
        JSON.stringify({
          url: normalized,
          createdAt: Date.now()
        })
      );
    } catch {
      // Ignore storage write errors.
    }
  }

  function readCompletionReturnUrl() {
    try {
      const raw = sessionStorage.getItem(COMPLETION_RETURN_KEY);
      if (!raw) return '';
      const parsed = JSON.parse(raw);
      const url = normalizeText(parsed && parsed.url ? parsed.url : '');
      const createdAt = Number(parsed && parsed.createdAt ? parsed.createdAt : 0);
      if (!url) return '';
      // Auto-expire stale redirect intents.
      if (!Number.isFinite(createdAt) || Date.now() - createdAt > 10 * 60 * 1000) {
        sessionStorage.removeItem(COMPLETION_RETURN_KEY);
        return '';
      }
      return url;
    } catch {
      return '';
    }
  }

  function hasCompletionRedirectIntent() {
    return !!readCompletionReturnUrl();
  }

  function writeRunLockFlag(ttlMs = 10 * 60 * 1000) {
    const ttl = Math.max(1000, Number(ttlMs) || 0);
    try {
      sessionStorage.setItem(
        RUN_LOCK_KEY,
        JSON.stringify({
          expiresAt: Date.now() + ttl
        })
      );
    } catch {
      // Ignore storage write errors.
    }
  }

  function hasRunLockFlag() {
    try {
      const raw = sessionStorage.getItem(RUN_LOCK_KEY);
      if (!raw) return false;
      const parsed = JSON.parse(raw);
      const expiresAt = Number(parsed && parsed.expiresAt ? parsed.expiresAt : 0);
      if (!Number.isFinite(expiresAt) || Date.now() > expiresAt) {
        sessionStorage.removeItem(RUN_LOCK_KEY);
        return false;
      }
      return true;
    } catch {
      return false;
    }
  }

  function clearRunLockFlag() {
    try {
      sessionStorage.removeItem(RUN_LOCK_KEY);
    } catch {
      // Ignore storage issues.
    }
  }

  function clearCompletionReturnUrl() {
    try {
      sessionStorage.removeItem(COMPLETION_RETURN_KEY);
      sessionStorage.removeItem(COMPLETION_REDIRECT_GUARD_KEY);
      sessionStorage.removeItem(CANCEL_LANDING_REDIRECT_GUARD_KEY);
    } catch {
      // Ignore storage issues.
    }
  }

  function maybeRedirectAfterCompletion() {
    if (isSubscriptionListPage()) return false;

    const target = readCompletionReturnUrl();
    if (!target) return false;
    if (normalizeUrl(target) === normalizeUrl(location.href)) {
      clearCompletionReturnUrl();
      return false;
    }

    if (shouldThrottleRedirect(COMPLETION_REDIRECT_GUARD_KEY, target)) return false;

    return redirectWithLockDelay(target);
  }

  function maybeRedirectFromCancelLanding() {
    if (isSubscriptionListPage()) return false;
    if (!isFmcCancelResultPage()) return false;

    const job = readStoredJob();
    let target = '';

    if (job && Array.isArray(job.pending) && job.pending.length > 0) {
      target = getJobResumeUrl(job);
    } else {
      target = readCompletionReturnUrl() || readLastSubscriptionListUrl() || buildSubscriptionListUrl(extractShipIdFromUrl(location.href));
    }

    if (!target) return false;
    if (normalizeUrl(target) === normalizeUrl(location.href)) return false;
    if (shouldThrottleRedirect(CANCEL_LANDING_REDIRECT_GUARD_KEY, target, 10000)) return false;

    return redirectWithLockDelay(target);
  }

  function buildJobStatusText(job, stoppedEarly = false) {
    const successCount = Array.isArray(job.done) ? job.done.length : 0;
    const failureCount = Array.isArray(job.failed) ? job.failed.length : 0;
    const remainingCount = Array.isArray(job.pending) ? job.pending.length : 0;

    if (stoppedEarly || remainingCount > 0) {
      return `Stopped. Success: ${successCount}, Failed: ${failureCount}, Remaining: ${remainingCount}`;
    }

    return `Done. Success: ${successCount}, Failed: ${failureCount}`;
  }

  function getClickableElements(scope = document) {
    const raw = Array.from(scope.querySelectorAll(CONFIG.clickableSelector));
    const deduped = [];
    const seen = new Set();

    for (const el of raw) {
      let keyEl = el;
      if (el.matches('span.a-button-text, span.a-button-inner')) {
        keyEl = el.closest('span.a-button') || el;
      } else if (el.matches('input.a-button-input')) {
        keyEl = el.closest('span.a-button') || el;
      }
      if (!keyEl) continue;
      if (seen.has(keyEl)) continue;
      seen.add(keyEl);
      deduped.push(keyEl);
    }

    return deduped;
  }

  function resolveClickTarget(el) {
    if (!el || !(el instanceof Element)) return null;
    if (el.matches('span.a-button-text, span.a-button-inner')) {
      const amazonButton = el.closest('span.a-button');
      if (amazonButton) {
        const input = amazonButton.querySelector('input.a-button-input, input[type="button"], input[type="submit"]');
        return input || amazonButton;
      }
    }
    if (el.matches('span.a-button')) {
      const input = el.querySelector('input.a-button-input, input[type="button"], input[type="submit"]');
      return input || el;
    }
    if (el.matches(CONFIG.clickTargetSelector)) return el;
    const ancestor = el.closest(CONFIG.clickTargetSelector);
    if (ancestor) {
      if (ancestor.matches('span.a-button')) {
        const input = ancestor.querySelector('input.a-button-input, input[type="button"], input[type="submit"]');
        return input || ancestor;
      }
      return ancestor;
    }
    return el;
  }

  function findControlsByPatterns(regexes, scope = document, excludeSet = null) {
    const controls = getClickableElements(scope);
    for (const el of controls) {
      if (excludeSet && excludeSet.has(el)) continue;
      if (!isVisible(el) || isDisabled(el)) continue;
      const clickTarget = resolveClickTarget(el);
      const label = normalizeText(`${getElementText(el)} ${getElementText(clickTarget)}`);
      if (!label) continue;
      if (textMatchesAny(label, regexes)) return el;
    }
    return null;
  }

  function getActiveDialogScope() {
    const candidates = Array.from(
      document.querySelectorAll(
        '[role="dialog"], [aria-modal="true"], .a-modal-scroller, .a-modal-container, .a-popover, .a-sheet, [data-a-modal]'
      )
    );
    return candidates.find((el) => isVisible(el)) || null;
  }

  function safeClick(el) {
    const target = resolveClickTarget(el);
    if (!target) return false;
    target.scrollIntoView({ behavior: 'smooth', block: 'center', inline: 'center' });
    const rect = target.getBoundingClientRect();
    const init = {
      bubbles: true,
      cancelable: true,
      view: window,
      clientX: rect.left + Math.max(1, rect.width / 2),
      clientY: rect.top + Math.max(1, rect.height / 2)
    };
    ['pointerdown', 'mousedown', 'mouseup', 'click'].forEach((type) => {
      target.dispatchEvent(new MouseEvent(type, init));
    });
    return true;
  }

  function hashString(input) {
    let hash = 5381;
    for (let i = 0; i < input.length; i += 1) {
      hash = (hash * 33) ^ input.charCodeAt(i);
    }
    return (hash >>> 0).toString(36);
  }

  function extractTitle(card) {
    const selectors = [
      'h1',
      'h2',
      'h3',
      '.a-size-base-plus',
      '.a-size-medium',
      '[data-a-word-break="normal"]',
      'a[href*="/dp/"]',
      'img[alt]'
    ];
    for (const selector of selectors) {
      const el = card.querySelector(selector);
      if (!el) continue;
      const text = selector === 'img[alt]' ? el.getAttribute('alt') : getElementText(el);
      const clean = normalizeText(text);
      if (clean && clean.length > 3) return clean.slice(0, 140);
    }
    return 'Subscription item';
  }

  function selectCardContainer(editControl) {
    let el = editControl;
    let fallback = null;

    while (el && el !== document.body) {
      if (el.matches && el.matches('li, article, section, .a-box, .a-section, div')) {
        const rect = el.getBoundingClientRect();
        const largeEnough = rect.width >= 220 && rect.height >= 60;
        if (largeEnough && !fallback) fallback = el;
        if (largeEnough) {
          const editCount = getClickableElements(el)
            .filter((node) => isVisible(node))
            .map((node) => getElementText(node))
            .filter((label) => textMatchesAny(label, CONFIG.editPatterns)).length;
          if (editCount === 1) return el;
        }
      }
      el = el.parentElement;
    }

    return fallback;
  }

  function cleanupStaleOverlays(validSubscriptions) {
    const validIds = new Set(validSubscriptions.map((item) => item.id));
    const validCards = new Set(validSubscriptions.map((item) => item.card));

    document.querySelectorAll('.amz-bulk-unsub-checkbox').forEach((el) => {
      const id = normalizeText(el.getAttribute('data-amz-id') || '');
      const card = el.closest('.amz-bulk-unsub-card, .subscription-card-item, .subscription-card');
      if (!id || !validIds.has(id) || !card || !validCards.has(card)) {
        el.remove();
      }
    });

    document.querySelectorAll('.amz-bulk-unsub-card').forEach((card) => {
      if (!validCards.has(card)) {
        card.classList.remove('amz-bulk-unsub-card', 'amz-bulk-unsub-selected');
      }
    });
  }

  function buildSubscriptionId(card, editControl, title) {
    const stableBits = [
      card.getAttribute('data-subscription-id') || '',
      card.getAttribute('data-asin') || '',
      card.getAttribute('data-csa-c-item-id') || '',
      editControl.getAttribute('href') || '',
      title || ''
    ].filter(Boolean);

    const raw = stableBits.join('|');
    if (!raw) {
      const fallback = `${title}|${Math.round(card.getBoundingClientRect().top + window.scrollY)}`;
      return `sub-${hashString(fallback)}`;
    }
    return `sub-${hashString(raw)}`;
  }

  function getEditControls() {
    const controls = getClickableElements(document);
    return controls.filter((el) => {
      if (!isVisible(el) || isDisabled(el)) return false;
      const text = getElementText(el);
      const ariaLabel = normalizeText(el.getAttribute('aria-label') || '');
      if (!text && !ariaLabel) return false;

      const sourceText = normalizeText(`${text} ${ariaLabel}`);
      if (textMatchesAny(sourceText, CONFIG.editExcludePatterns)) return false;
      if (textMatchesAny(ariaLabel, CONFIG.editPatterns)) return true;
      if (textMatchesAny(text, CONFIG.editPatterns)) return true;
      return false;
    });
  }

  function getItemEditControls() {
    const direct = Array.from(document.querySelectorAll('input.a-button-input[aria-label]')).filter((el) => {
      if (!isVisible(el) || isDisabled(el)) return false;
      const ariaLabel = normalizeText(el.getAttribute('aria-label') || '');
      return /^\s*edit\s*,/i.test(ariaLabel);
    });

    if (direct.length) return direct;
    return getEditControls();
  }

  function discoverSubscriptions() {
    const result = [];
    const seenCards = new Set();
    const editControls = getItemEditControls();

    for (const editControl of editControls) {
      const card =
        editControl.closest('.subscription-card-item, .subscription-card') || selectCardContainer(editControl);
      if (!card || seenCards.has(card)) continue;
      seenCards.add(card);
      const title = extractTitle(card);
      const id = buildSubscriptionId(card, editControl, title);
      result.push({ id, title, card, editControl });
    }

    result.sort((a, b) => a.card.getBoundingClientRect().top - b.card.getBoundingClientRect().top);
    return result;
  }

  function onToggleSelection(id, checked, card) {
    if (checked) {
      STATE.selectedIds.add(id);
      card.classList.add('amz-bulk-unsub-selected');
    } else {
      STATE.selectedIds.delete(id);
      card.classList.remove('amz-bulk-unsub-selected');
    }
    updateCounts();
  }

  function attachCardCheckbox(item) {
    const { id, title, card } = item;
    card.classList.add('amz-bulk-unsub-card');
    if (window.getComputedStyle(card).position === 'static') {
      card.style.position = 'relative';
    }

    let wrap = card.querySelector('.amz-bulk-unsub-checkbox');
    const currentId = wrap ? normalizeText(wrap.getAttribute('data-amz-id') || '') : '';
    if (wrap && currentId && currentId !== id) {
      wrap.remove();
      wrap = null;
    }

    if (!wrap) {
      wrap = document.createElement('label');
      wrap.className = 'amz-bulk-unsub-checkbox';
      // Enforce top-left placement even if page styles override class rules.
      wrap.style.setProperty('top', '10px', 'important');
      wrap.style.setProperty('left', '10px', 'important');
      wrap.style.setProperty('right', 'auto', 'important');
      wrap.style.setProperty('inset-inline-start', '10px', 'important');
      wrap.style.setProperty('inset-inline-end', 'auto', 'important');

      const checkbox = document.createElement('input');
      checkbox.type = 'checkbox';
      checkbox.className = 'amz-bulk-unsub-toggle';
      checkbox.addEventListener('change', () => {
        const activeId = normalizeText(wrap.getAttribute('data-amz-id') || id);
        onToggleSelection(activeId, checkbox.checked, card);
      });

      const label = document.createElement('span');
      label.className = 'amz-bulk-unsub-label';
      label.textContent = 'Select';

      wrap.appendChild(checkbox);
      wrap.appendChild(label);
      card.appendChild(wrap);
    }

    wrap.setAttribute('data-amz-id', id);
    wrap.title = title;
    const checkbox = wrap.querySelector('.amz-bulk-unsub-toggle');
    if (checkbox) {
      checkbox.checked = STATE.selectedIds.has(id);
      if (checkbox.checked) {
        card.classList.add('amz-bulk-unsub-selected');
      } else {
        card.classList.remove('amz-bulk-unsub-selected');
      }
    }
  }

  function updateCounts() {
    if (!STATE.countEl) return;
    STATE.countEl.textContent = `${STATE.selectedIds.size} selected / ${STATE.subscriptions.length} found`;
  }

  function setStatus(text, isError = false) {
    if (!STATE.statusEl) return;
    STATE.statusEl.textContent = text;
    STATE.statusEl.style.color = isError ? '#b91c1c' : '#111827';
  }

  function refreshSubscriptions() {
    STATE.suppressObserver = true;
    try {
      const discovered = discoverSubscriptions();
      cleanupStaleOverlays(discovered);
      STATE.subscriptions = discovered;

      const validIds = new Set(discovered.map((item) => item.id));
      for (const id of Array.from(STATE.selectedIds)) {
        if (!validIds.has(id)) STATE.selectedIds.delete(id);
      }

      discovered.forEach((item) => attachCardCheckbox(item));
      updateCounts();
      if (!STATE.running) setStatus('Ready');
    } finally {
      setTimeout(() => {
        STATE.suppressObserver = false;
      }, 0);
    }
  }

  function findItemById(id) {
    return STATE.subscriptions.find((item) => item.id === id) || null;
  }

  function findItemByTitle(title) {
    const normalized = normalizeText(title).toLowerCase();
    if (!normalized) return null;

    const exact = STATE.subscriptions.find((item) => normalizeText(item.title).toLowerCase() === normalized);
    if (exact) return exact;

    return (
      STATE.subscriptions.find((item) => {
        const candidate = normalizeText(item.title).toLowerCase();
        return candidate.includes(normalized) || normalized.includes(candidate);
      }) || null
    );
  }

  function findItemForEntry(entry) {
    const normalizedEntry = normalizeJobEntry(entry);
    if (!normalizedEntry) return null;

    if (normalizedEntry.id) {
      const byId = findItemById(normalizedEntry.id);
      if (byId) return byId;
    }

    return findItemByTitle(normalizedEntry.title);
  }

  async function waitForEntryToAppear(entry, timeoutMs = CONFIG.resumeFindTimeoutMs) {
    const start = Date.now();
    let scrollDown = false;
    let lastNudgeAt = 0;

    while (Date.now() - start < timeoutMs) {
      refreshSubscriptions();
      const target = findItemForEntry(entry);
      if (target) return target;

      // Nudge lazy-loaded lists less often to reduce visible page jumping.
      if (Date.now() - lastNudgeAt >= CONFIG.scrollNudgeMs) {
        if (scrollDown) {
          window.scrollTo({ top: document.body.scrollHeight, behavior: 'auto' });
        } else {
          window.scrollTo({ top: 0, behavior: 'auto' });
        }
        scrollDown = !scrollDown;
        lastNudgeAt = Date.now();
      }

      await sleep(CONFIG.resumePollMs);
    }

    refreshSubscriptions();
    return findItemForEntry(entry);
  }

  function removePendingEntry(job, entry) {
    const idx = job.pending.findIndex((pendingEntry) => entriesMatch(pendingEntry, entry));
    if (idx < 0) return null;
    return job.pending.splice(idx, 1)[0] || null;
  }

  async function reconcileInFlightAfterNavigation(job) {
    if (!job || !job.inFlight) return;

    const inFlight = normalizeJobEntry(job.inFlight);
    job.inFlight = null;
    if (!inFlight) {
      writeStoredJob(job);
      return;
    }

    const start = Date.now();
    while (Date.now() - start < CONFIG.resumeFindTimeoutMs) {
      refreshSubscriptions();
      const stillVisible = findItemForEntry(inFlight);
      if (stillVisible) {
        log(`Resuming unfinished item: ${inFlight.title}`);
        writeStoredJob(job);
        return;
      }

      // Once list content is present and the in-flight item is gone, treat it as completed.
      if (STATE.subscriptions.length > 0) {
        const removed = removePendingEntry(job, inFlight) || inFlight;
        job.done.push(removed);
        log(`Recovered after redirect: ${removed.title}`);
        writeStoredJob(job);
        return;
      }

      await sleep(CONFIG.resumePollMs);
    }

    // Timeout while page is still unstable; keep queue and let main loop retry.
    log(`Could not confirm previous item after redirect yet: ${inFlight.title}`);
    writeStoredJob(job);
  }

  function scheduleRefresh() {
    if (STATE.running || STATE.suppressObserver) return;
    clearTimeout(STATE.refreshTimer);
    STATE.refreshTimer = setTimeout(() => {
      STATE.refreshTimer = null;
      refreshSubscriptions();
    }, CONFIG.observerRefreshMs);
  }

  function isInteractionLocked() {
    if (STATE.running) return true;
    if (isSubscriptionListPage()) return false;
    return hasRunLockFlag() || hasActiveStoredJob() || hasCompletionRedirectIntent();
  }

  function setStyleImportant(el, prop, value) {
    if (!el || !el.style) return;
    el.style.setProperty(prop, value, 'important');
  }

  function applyLockInlineStyles() {
    if (!STATE.lockEl) return;

    const lock = STATE.lockEl;
    setStyleImportant(lock, 'position', 'fixed');
    setStyleImportant(lock, 'inset', '0');
    setStyleImportant(lock, 'z-index', '2147483646');
    setStyleImportant(lock, 'background', 'rgba(15, 23, 42, 0.12)');
    setStyleImportant(lock, 'cursor', 'not-allowed');
    setStyleImportant(lock, 'user-select', 'none');
    setStyleImportant(lock, '-webkit-user-select', 'none');
    setStyleImportant(lock, 'opacity', '1');

    const message = lock.querySelector('.amz-bulk-lock-message');
    if (!message) return;
    setStyleImportant(message, 'position', 'fixed');
    setStyleImportant(message, 'left', '50%');
    setStyleImportant(message, 'top', '16px');
    setStyleImportant(message, 'transform', 'translateX(-50%)');
    setStyleImportant(message, 'padding', '8px 12px');
    setStyleImportant(message, 'border-radius', '999px');
    setStyleImportant(message, 'border', '1px solid #cbd5e1');
    setStyleImportant(message, 'background', 'rgba(255, 255, 255, 0.96)');
    setStyleImportant(message, 'color', '#0f172a');
    setStyleImportant(message, 'font', '600 12px/1.2 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif');
    setStyleImportant(message, 'box-shadow', '0 6px 18px rgba(15, 23, 42, 0.22)');
    setStyleImportant(message, 'pointer-events', 'none');
    setStyleImportant(message, 'white-space', 'nowrap');
    setStyleImportant(message, 'z-index', '2147483647');
    setStyleImportant(message, 'display', 'block');
  }

  function setInteractionLockVisibility(locked) {
    if (!STATE.lockEl) return;
    setStyleImportant(STATE.lockEl, 'display', locked ? 'block' : 'none');
    setStyleImportant(STATE.lockEl, 'pointer-events', locked ? 'auto' : 'none');
    STATE.lockEl.setAttribute('aria-hidden', locked ? 'false' : 'true');
  }

  function updateButtonStates() {
    const running = STATE.running;
    const locked = isInteractionLocked();
    if (STATE.runBtn) STATE.runBtn.disabled = running;
    if (STATE.stopBtn) STATE.stopBtn.disabled = !running;
    document.documentElement.classList.toggle('amz-bulk-running', locked);
    if ((locked || STATE.lockEl) && !STATE.lockEl) {
      createInteractionLockLayer();
    }
    if (STATE.lockEl && !STATE.lockEl.isConnected && document.body) {
      document.body.appendChild(STATE.lockEl);
    }
    if (STATE.lockEl) {
      applyLockInlineStyles();
      setInteractionLockVisibility(locked);
    }
    if (running && STATE.stopBtn) {
      STATE.stopBtn.focus({ preventScroll: true });
    }
  }

  function handleGlobalPointerGuard(event) {
    if (!isInteractionLocked()) return;
    // Allow script-generated events so automation can continue.
    if (!event.isTrusted) return;
    if (STATE.panel && STATE.panel.contains(event.target)) return;
    event.preventDefault();
    event.stopPropagation();
    if (typeof event.stopImmediatePropagation === 'function') {
      event.stopImmediatePropagation();
    }
    if (STATE.stopBtn) STATE.stopBtn.focus({ preventScroll: true });
  }

  function handleGlobalKeydownGuard(event) {
    if (!isInteractionLocked()) return;
    // Allow script-generated events so automation can continue.
    if (!event.isTrusted) return;
    if (STATE.panel && STATE.panel.contains(event.target)) return;
    event.preventDefault();
    event.stopPropagation();
    if (typeof event.stopImmediatePropagation === 'function') {
      event.stopImmediatePropagation();
    }
  }

  function createInteractionLockLayer() {
    if (STATE.lockEl && STATE.lockEl.isConnected) {
      applyLockInlineStyles();
      setInteractionLockVisibility(isInteractionLocked());
      return;
    }
    const lock = document.createElement('div');
    lock.id = 'amz-bulk-interaction-lock';
    lock.setAttribute('aria-hidden', 'true');
    lock.innerHTML = `<div class="amz-bulk-lock-message">Automation running. Use panel controls only.</div>`;

    ['click', 'dblclick', 'mousedown', 'mouseup', 'pointerdown', 'pointerup', 'touchstart', 'touchmove', 'contextmenu', 'wheel'].forEach(
      (type) => {
        lock.addEventListener(type, handleGlobalPointerGuard, { capture: true, passive: false });
      }
    );

    document.body.appendChild(lock);
    STATE.lockEl = lock;
    applyLockInlineStyles();
    setInteractionLockVisibility(isInteractionLocked());

    if (!STATE.keyboardGuardBound) {
      document.addEventListener('keydown', handleGlobalKeydownGuard, true);
      STATE.keyboardGuardBound = true;
    }

    if (!STATE.pointerGuardBound) {
      ['click', 'dblclick', 'mousedown', 'mouseup', 'pointerdown', 'pointerup', 'touchstart', 'touchmove', 'contextmenu', 'wheel'].forEach(
        (type) => {
          document.addEventListener(type, handleGlobalPointerGuard, { capture: true, passive: false });
        }
      );
      STATE.pointerGuardBound = true;
    }
  }

  function selectAllVisible() {
    STATE.subscriptions.forEach((item) => STATE.selectedIds.add(item.id));
    refreshSubscriptions();
  }

  function clearSelection() {
    STATE.selectedIds.clear();
    refreshSubscriptions();
  }

  function showBulkConfirmDialog(targets) {
    return new Promise((resolve) => {
      const existing = document.getElementById('amz-bulk-confirm-overlay');
      if (existing) existing.remove();

      const maxItemsShown = 60;
      const hiddenCount = Math.max(0, targets.length - maxItemsShown);
      const listMarkup = targets
        .slice(0, maxItemsShown)
        .map((item) => `<li>${escapeHtml(item.title || 'Subscription item')}</li>`)
        .join('');

      const hiddenMarkup =
        hiddenCount > 0 ? `<div class="amz-confirm-more">...and ${hiddenCount} more item(s)</div>` : '';

      const overlay = document.createElement('div');
      overlay.id = 'amz-bulk-confirm-overlay';
      overlay.innerHTML = `
        <div class="amz-bulk-confirm-dialog" role="dialog" aria-modal="true" aria-label="Confirm bulk unsubscribe">
          <div class="amz-confirm-title">Confirm Bulk Unsubscribe</div>
          <div class="amz-confirm-subtitle">${targets.length} subscription(s) will be unsubscribed:</div>
          <ul class="amz-confirm-list">${listMarkup}</ul>
          ${hiddenMarkup}
          <div class="amz-confirm-actions">
            <button type="button" id="amz-confirm-cancel">Cancel</button>
            <button type="button" id="amz-confirm-ok" class="amz-confirm-danger">Confirm unsubscribe</button>
          </div>
        </div>
      `;

      const cleanup = (result) => {
        window.removeEventListener('keydown', onKeydown);
        overlay.remove();
        resolve(result);
      };

      const onKeydown = (event) => {
        if (event.key === 'Escape') cleanup(false);
      };

      const cancelBtn = overlay.querySelector('#amz-confirm-cancel');
      const okBtn = overlay.querySelector('#amz-confirm-ok');

      cancelBtn.addEventListener('click', () => cleanup(false));
      okBtn.addEventListener('click', () => cleanup(true));
      overlay.addEventListener('click', (event) => {
        if (event.target === overlay) cleanup(false);
      });
      window.addEventListener('keydown', onKeydown);

      document.body.appendChild(overlay);
      okBtn.focus();
    });
  }

  async function findStepControl(stepPatterns, contextItem, excluded) {
    const excludeSet = new Set(excluded || []);
    const control = await waitFor(() => {
      const scopes = [];
      const dialog = getActiveDialogScope();
      if (dialog) scopes.push(dialog);
      if (contextItem && contextItem.card && !scopes.includes(contextItem.card)) {
        scopes.push(contextItem.card);
      }
      scopes.push(document);

      for (const scope of scopes) {
        const el = findControlsByPatterns(stepPatterns, scope, excludeSet);
        if (el) return el;
      }
      return null;
    }, CONFIG.waitTimeoutMs);

    return control;
  }

  async function runSingleUnsubscribe(item, idx, total) {
    const title = item.title || `Subscription ${idx + 1}`;
    setStatus(`[${idx + 1}/${total}] ${title}`);
    log(`Processing ${idx + 1}/${total}: ${title}`);

    let current = findItemById(item.id);
    if (!current) {
      refreshSubscriptions();
      current = findItemById(item.id);
    }
    if (!current) {
      throw new Error('Subscription card is no longer visible');
    }

    const editControl = current.editControl;
    if (!editControl || !isVisible(editControl)) {
      throw new Error('Edit control not found/visible');
    }

    safeClick(editControl);
    await sleep(CONFIG.clickPauseMs);

    const cancelStep1 = await findStepControl(CONFIG.cancelStep1Patterns, current, [editControl]);
    if (!cancelStep1) {
      throw new Error('Could not find first cancel action after clicking Edit');
    }
    safeClick(cancelStep1);
    await sleep(CONFIG.clickPauseMs);

    const cancelStep2 = await findStepControl(CONFIG.cancelStep2Patterns, current, [editControl, cancelStep1]);
    if (!cancelStep2) {
      throw new Error('Could not find second confirm-cancel action');
    }
    safeClick(cancelStep2);
    await sleep(CONFIG.clickPauseMs + 400);
  }

  async function runStoredJob(job, { resumed = false } = {}) {
    if (!job || !Array.isArray(job.pending) || !job.pending.length) return;
    if (STATE.running) return;

    STATE.running = true;
    STATE.stopRequested = false;
    writeRunLockFlag();
    clearCompletionReturnUrl();
    updateButtonStates();
    setStatus(`${resumed ? 'Resuming' : 'Starting'} bulk unsubscribe (${job.pending.length} remaining)`);

    let stoppedEarly = false;

    try {
      refreshSubscriptions();
      await reconcileInFlightAfterNavigation(job);

      while (job.pending.length) {
        if (STATE.stopRequested) {
          stoppedEarly = true;
          log('Stop requested. Ending after current item.');
          break;
        }

        refreshSubscriptions();
        const nextEntry = normalizeJobEntry(job.pending[0]);
        if (!nextEntry) {
          job.pending.shift();
          writeStoredJob(job);
          continue;
        }

        const target = await waitForEntryToAppear(nextEntry);
        if (!target) {
          const missingEntry = job.pending.shift() || nextEntry;
          job.failed.push({
            ...(normalizeJobEntry(missingEntry) || nextEntry),
            error: 'Could not find this subscription on the refreshed page'
          });
          writeStoredJob(job);
          log(`Failed: not found after refresh wait: ${missingEntry.title}`, 'error');
          continue;
        }

        const total = job.done.length + job.failed.length + job.pending.length;
        const currentIndex = job.done.length + job.failed.length;

        job.pending[0] = normalizeJobEntry({ id: target.id, title: target.title }) || nextEntry;
        job.inFlight = normalizeJobEntry({ id: target.id, title: target.title });
        writeStoredJob(job);

        try {
          await runSingleUnsubscribe(target, currentIndex, total);
          const doneEntry = job.pending.shift() || job.inFlight || nextEntry;
          job.done.push(normalizeJobEntry(doneEntry) || nextEntry);
          job.inFlight = null;
          writeStoredJob(job);
          STATE.selectedIds.delete(target.id);
          log(`Success: ${target.title}`);
        } catch (err) {
          const failedEntry = job.pending.shift() || job.inFlight || nextEntry;
          job.failed.push({
            ...(normalizeJobEntry(failedEntry) || nextEntry),
            error: err && err.message ? err.message : String(err)
          });
          job.inFlight = null;
          writeStoredJob(job);
          log(`Failed: ${target.title} (${err && err.message ? err.message : 'Unknown error'})`, 'error');
        }

        refreshSubscriptions();
        await sleep(CONFIG.betweenItemsPauseMs);
      }
    } finally {
      STATE.running = false;
      updateButtonStates();
      refreshSubscriptions();

      if (stoppedEarly) {
        clearStoredJob();
        clearRunLockFlag();
        clearCompletionReturnUrl();
        const stoppedStatus = buildJobStatusText(job, true);
        setStatus(stoppedStatus, job.failed.length > 0);
        alert(stoppedStatus);
        return;
      }

      if (job.pending.length === 0) {
        clearStoredJob();
        const completionReturnUrl = getJobResumeUrl(job);
        writeCompletionReturnUrl(completionReturnUrl);
        const doneStatus = buildJobStatusText(job, false);
        setStatus(doneStatus, job.failed.length > 0);
        alert(doneStatus);
        if (normalizeUrl(location.href) !== normalizeUrl(completionReturnUrl)) {
          location.assign(completionReturnUrl);
        }
      } else {
        // Remaining items will be resumed automatically after redirect/reload.
        writeStoredJob(job);
        setStatus(`In progress (${job.pending.length} remaining)...`);
      }
    }
  }

  async function maybeResumeStoredJob() {
    if (!isSubscriptionListPage()) return;
    if (STATE.running) return;

    const job = readStoredJob();
    if (!job) return;

    if (!Array.isArray(job.pending) || job.pending.length === 0) {
      clearStoredJob();
      return;
    }

    log(`Resuming saved job with ${job.pending.length} remaining item(s).`);
    await runStoredJob(job, { resumed: true });
  }

  async function runBulkUnsubscribe() {
    if (STATE.running) return;

    const targets = STATE.subscriptions.filter((item) => STATE.selectedIds.has(item.id));
    if (!targets.length) {
      alert('Select at least one subscription first.');
      return;
    }

    const confirmed = await showBulkConfirmDialog(targets);
    if (!confirmed) {
      setStatus('Cancelled by user');
      return;
    }

    clearStoredJob();
    const job = createStoredJob(targets);
    writeStoredJob(job);
    await runStoredJob(job, { resumed: false });
  }

  function injectStyles() {
    const style = document.createElement('style');
    style.textContent = `
      .amz-bulk-unsub-card {
        outline: 2px solid transparent;
        transition: outline-color 120ms ease-in-out, box-shadow 120ms ease-in-out;
      }

      .amz-bulk-unsub-selected {
        outline-color: #ef4444 !important;
        box-shadow: 0 0 0 3px rgba(239, 68, 68, 0.25) !important;
      }

      .amz-bulk-unsub-checkbox {
        position: absolute;
        top: 10px !important;
        left: 10px !important;
        right: auto !important;
        z-index: 9998;
        display: flex;
        flex-direction: row;
        align-items: center;
        justify-content: flex-start;
        gap: 6px;
        padding: 6px 10px;
        border: 1px solid rgba(17, 24, 39, 0.18);
        border-radius: 999px;
        background: rgba(255, 255, 255, 0.96);
        color: #0f172a;
        font-size: 12px;
        font-weight: 600;
        line-height: 1.2;
        box-shadow: 0 4px 14px rgba(15, 23, 42, 0.16);
        backdrop-filter: blur(1px);
        user-select: none;
        cursor: pointer;
        margin: 0;
        white-space: nowrap;
        transition: transform 120ms ease, box-shadow 120ms ease, border-color 120ms ease;
      }

      .amz-bulk-unsub-card:hover .amz-bulk-unsub-checkbox {
        transform: translateY(-1px);
        box-shadow: 0 8px 18px rgba(15, 23, 42, 0.2);
      }

      .amz-bulk-unsub-checkbox .amz-bulk-unsub-toggle {
        margin: 0;
        width: 15px;
        height: 15px;
        flex: 0 0 auto;
        accent-color: #dc2626;
        cursor: pointer;
        vertical-align: middle;
      }

      .amz-bulk-unsub-checkbox .amz-bulk-unsub-label {
        display: inline-block;
        letter-spacing: 0.01em;
        line-height: 1;
        vertical-align: middle;
      }

      .amz-bulk-running .amz-bulk-unsub-checkbox {
        display: none !important;
      }

      #amz-bulk-interaction-lock {
        position: fixed;
        inset: 0;
        z-index: 2147483646;
        display: none;
        pointer-events: none;
        background: rgba(15, 23, 42, 0.08);
        cursor: not-allowed;
      }

      .amz-bulk-running #amz-bulk-interaction-lock {
        display: block;
        pointer-events: auto;
      }

      #amz-bulk-interaction-lock .amz-bulk-lock-message {
        position: fixed;
        left: 50%;
        top: 16px;
        transform: translateX(-50%);
        padding: 8px 12px;
        border-radius: 999px;
        border: 1px solid #cbd5e1;
        background: rgba(255, 255, 255, 0.94);
        color: #0f172a;
        font: 12px/1.2 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
        box-shadow: 0 6px 18px rgba(15, 23, 42, 0.22);
        user-select: none;
        pointer-events: none;
      }

      #amz-bulk-unsub-panel {
        position: fixed;
        right: 16px;
        bottom: 16px;
        width: 340px;
        z-index: 2147483647;
        background: #ffffff;
        color: #111827;
        border: 1px solid #d1d5db;
        border-radius: 12px;
        box-shadow: 0 12px 32px rgba(0, 0, 0, 0.28);
        padding: 12px;
        font: 13px/1.35 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      }

      #amz-bulk-unsub-panel .amz-bulk-title {
        font-weight: 700;
        font-size: 14px;
        margin-bottom: 8px;
      }

      #amz-bulk-unsub-panel .amz-bulk-row {
        display: flex;
        gap: 8px;
        align-items: center;
        margin-top: 8px;
      }

      #amz-bulk-unsub-panel button {
        border: 1px solid #9ca3af;
        background: #f9fafb;
        color: #111827;
        border-radius: 8px;
        padding: 6px 9px;
        font-size: 12px;
        cursor: pointer;
      }

      #amz-bulk-unsub-panel button:hover:enabled {
        background: #f3f4f6;
      }

      #amz-bulk-unsub-panel button:disabled {
        opacity: 0.5;
        cursor: not-allowed;
      }

      #amz-bulk-unsub-panel .amz-bulk-danger {
        border-color: #dc2626;
        background: #ef4444;
        color: #ffffff;
        font-weight: 600;
      }

      #amz-bulk-unsub-panel .amz-bulk-danger:hover:enabled {
        background: #dc2626;
      }

      #amz-bulk-unsub-status {
        margin-top: 8px;
        font-weight: 600;
      }

      #amz-bulk-unsub-log {
        margin-top: 8px;
        height: 120px;
        overflow: auto;
        background: #f8fafc;
        border: 1px solid #e5e7eb;
        border-radius: 8px;
        padding: 8px;
        white-space: pre-wrap;
        font: 11px/1.25 ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
      }

      #amz-bulk-confirm-overlay {
        position: fixed;
        inset: 0;
        background: rgba(15, 23, 42, 0.55);
        z-index: 2147483647;
        display: flex;
        align-items: center;
        justify-content: center;
        padding: 16px;
      }

      .amz-bulk-confirm-dialog {
        width: min(700px, 96vw);
        max-height: 86vh;
        overflow: hidden;
        background: #ffffff;
        border: 1px solid #d1d5db;
        border-radius: 12px;
        box-shadow: 0 18px 50px rgba(0, 0, 0, 0.35);
        padding: 16px;
        color: #111827;
      }

      .amz-confirm-title {
        font-size: 16px;
        font-weight: 700;
        margin-bottom: 8px;
      }

      .amz-confirm-subtitle {
        font-size: 13px;
        margin-bottom: 8px;
      }

      .amz-confirm-list {
        margin: 0;
        padding-left: 18px;
        max-height: 48vh;
        overflow: auto;
        border: 1px solid #e5e7eb;
        border-radius: 8px;
        background: #f8fafc;
      }

      .amz-confirm-list li {
        margin: 6px 8px 6px 0;
        line-height: 1.3;
        font-size: 12px;
      }

      .amz-confirm-more {
        margin-top: 6px;
        font-size: 12px;
        color: #4b5563;
      }

      .amz-confirm-actions {
        display: flex;
        justify-content: flex-end;
        gap: 8px;
        margin-top: 12px;
      }

      .amz-confirm-actions button {
        border: 1px solid #9ca3af;
        background: #f9fafb;
        color: #111827;
        border-radius: 8px;
        padding: 7px 10px;
        font-size: 12px;
        cursor: pointer;
      }

      .amz-confirm-actions button:hover {
        background: #f3f4f6;
      }

      .amz-confirm-actions .amz-confirm-danger {
        border-color: #dc2626;
        background: #ef4444;
        color: #ffffff;
        font-weight: 600;
      }

      .amz-confirm-actions .amz-confirm-danger:hover {
        background: #dc2626;
      }
    `;
    document.head.appendChild(style);
  }

  function createPanel() {
    const panel = document.createElement('div');
    panel.id = 'amz-bulk-unsub-panel';
    panel.innerHTML = `
      <div class="amz-bulk-title">Bulk Unsubscribe</div>
      <div id="amz-bulk-unsub-count">0 selected / 0 found</div>
      <div class="amz-bulk-row">
        <button type="button" id="amz-bulk-select-all">Select all visible</button>
        <button type="button" id="amz-bulk-clear">Clear</button>
      </div>
      <div class="amz-bulk-row">
        <button type="button" id="amz-bulk-run" class="amz-bulk-danger">Bulk unsubscribe</button>
        <button type="button" id="amz-bulk-stop" disabled>Stop</button>
      </div>
      <div id="amz-bulk-unsub-status">Loading...</div>
      <div id="amz-bulk-unsub-log"></div>
    `;
    document.body.appendChild(panel);

    STATE.panel = panel;
    STATE.countEl = panel.querySelector('#amz-bulk-unsub-count');
    STATE.statusEl = panel.querySelector('#amz-bulk-unsub-status');
    STATE.runBtn = panel.querySelector('#amz-bulk-run');
    STATE.stopBtn = panel.querySelector('#amz-bulk-stop');
    STATE.logEl = panel.querySelector('#amz-bulk-unsub-log');
    createInteractionLockLayer();

    panel.querySelector('#amz-bulk-select-all').addEventListener('click', selectAllVisible);
    panel.querySelector('#amz-bulk-clear').addEventListener('click', clearSelection);
    panel.querySelector('#amz-bulk-run').addEventListener('click', runBulkUnsubscribe);
    panel.querySelector('#amz-bulk-stop').addEventListener('click', () => {
      STATE.stopRequested = true;
      setStatus('Stopping...');
    });
  }

  function startObserver() {
    if (STATE.observer) return;
    STATE.observer = new MutationObserver(() => scheduleRefresh());
    STATE.observer.observe(document.body, { childList: true, subtree: true });
  }

  function init() {
    const activeJob = hasActiveStoredJob();
    const completionPendingRedirect = hasCompletionRedirectIntent();
    const runLockActive = hasRunLockFlag();

    // If a job is in progress or completion redirect is pending and we are on an intermediate page,
    // lock interactions immediately to avoid accidental clicks/navigation.
    if (!isSubscriptionListPage() && (runLockActive || activeJob || completionPendingRedirect)) {
      injectStyles();
      createInteractionLockLayer();
      updateButtonStates();
    }

    if (isSubscriptionListPage()) {
      try {
        sessionStorage.removeItem(MANAGER_REDIRECT_GUARD_KEY);
        sessionStorage.removeItem(RESUME_REDIRECT_GUARD_KEY);
      } catch {
        // Ignore storage issues.
      }
      writeLastSubscriptionListUrl(location.href);
      clearCompletionReturnUrl();
      if (!activeJob) {
        clearRunLockFlag();
      }
    }

    if (isManagerViewPage() && maybeRedirectFromManagerPage()) {
      return;
    }

    if (maybeRedirectForPendingJob()) {
      return;
    }

    if (maybeRedirectFromCancelLanding()) {
      return;
    }

    if (maybeRedirectAfterCompletion()) {
      return;
    }

    if (!isSubscriptionListPage()) {
      return;
    }

    injectStyles();
    createPanel();
    refreshSubscriptions();
    startObserver();
    log('Script ready. Select subscriptions, then click "Bulk unsubscribe".');
    void maybeResumeStoredJob();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init, { once: true });
  } else {
    init();
  }
})();
