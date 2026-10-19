(() => {
  'use strict';

  /* ---------------------------------------------------------
     COLLAGE CREW engine
     Layout model: justified rows on a 16:9 canvas.
     - rows partition canvas height by weight
     - items partition row width by weight
     - resizing one item renormalises its row / the other rows,
       so "corresponding" neighbours shrink or grow automatically
     - LOCK: an item pinned to the cell aspect it had at lock time
     - WHITE SPACE mode: every item pinned to its natural aspect,
       leftover paper stays white, nothing is cropped
     --------------------------------------------------------- */

  const canvas = document.getElementById('canvas');
  const emptyState = document.getElementById('empty');
  const fileInput = document.getElementById('fileInput');
  const toastWrap = document.getElementById('toast');
  const hudImages = document.getElementById('hudImages');
  const hudRows = document.getElementById('hudRows');
  const hudLocked = document.getElementById('hudLocked');
  const hudSelected = document.getElementById('hudSelected');
  const gapRange = document.getElementById('gapRange');
  const gapVal = document.getElementById('gapVal');
  const wsCheck = document.getElementById('wsCheck');
  const modeLabel = document.getElementById('modeLabel');

  const DIRS = ['nw', 'n', 'ne', 'e', 'se', 's', 'sw', 'w'];
  const MIN = 44;               // min cell size in display px
  const EXPORT_W = 3200;
  const EXPORT_H = 1800;
  const CAR = 16 / 9;           // canvas aspect ratio (w / h)

  const state = {
    items: [],
    rows: [],
    selected: null,
    userModified: false,
    gap: 0,
    seq: 0,
    whitespace: false
  };

  const pad = n => String(n).padStart(2, '0');
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  const rowOf = item => state.rows.find(r => r.items.includes(item));
  const dispAR = it => (it.rot % 180 === 90) ? 1 / (it.ar || 1) : (it.ar || 1);

  /* ---------------------------------------------------------
     Layout solver
     --------------------------------------------------------- */

  function heightFractions() {
    const rows = state.rows;
    const n = rows.length;
    if (!n) return { h: [], T: 0 };

    const totalW = rows.reduce((s, r) => s + r.weight, 0) || 1;
    const h = rows.map(r => r.weight / totalW);

    if (state.whitespace) {
      // pinned images (crop OFF) keep their natural aspect: content width
      // of a row = sum(aspects) * h / canvasAR. Cropped frames only need
      // a min share. Shrink rows that overflow — leftover stays white.
      const dispW = canvas.clientWidth || 1280;
      const dispH = canvas.clientHeight || 720;
      const minF = MIN / dispW;
      const minH = MIN / dispH;
      for (let r = 0; r < n; r++) {
        let sumAr = 0;
        let nFree = 0;
        for (const i of rows[r].items) {
          if (i.crop) nFree++;
          else sumAr += dispAR(i);
        }
        if (!sumAr) continue;
        const capacity = Math.max(minH, (1 - nFree * minF) * CAR / sumAr);
        if (h[r] > capacity) h[r] = capacity;
      }
      // rows do NOT fill the canvas height here — leftover stays white
    } else {
      // locked items pin their width via: w = lockAR * h / canvasAR.
      // Give each row a max height so locked content fits, redistribute.
      const dispW = canvas.clientWidth || 1280;
      const minF = MIN / dispW;
      const caps = rows.map(row => {
        let sumLockAR = 0;
        let freeCount = 0;
        for (const i of row.items) {
          if (i.locked) sumLockAR += i.lockAR;
          else freeCount++;
        }
        if (!sumLockAR) return Infinity;
        const capacity = freeCount ? Math.max(0, 1 - freeCount * minF) : 1;
        return capacity * CAR / Math.max(sumLockAR, 1e-9);
      });

      for (let pass = 0; pass < n + 2; pass++) {
        let excess = 0;
        const capped = new Array(n).fill(false);
        for (let r = 0; r < n; r++) {
          if (h[r] > caps[r]) {
            excess += h[r] - caps[r];
            h[r] = caps[r];
            capped[r] = true;
          }
        }
        if (excess < 1e-9) break;
        let freeSum = 0;
        for (let r = 0; r < n; r++) if (!capped[r]) freeSum += h[r];
        if (freeSum < 1e-9) break;
        for (let r = 0; r < n; r++) if (!capped[r]) h[r] += excess * h[r] / freeSum;
      }
      // normal mode always fills the canvas height
      const T2 = h.reduce((s, v) => s + v, 0) || 1;
      for (let r = 0; r < n; r++) h[r] /= T2;
    }

    const T = h.reduce((s, v) => s + v, 0);
    return { h, T };
  }

  function rowCells(row, hr) {
    const items = row.items;

    if (state.whitespace) {
      const free = items.filter(i => i.crop);
      const pinnedW = i => dispAR(i) * hr / CAR;

      if (!free.length) {
        // every image pinned to its natural aspect — centre the group
        const cells = items.map(i => ({ item: i, w: pinnedW(i) }));
        const sum = cells.reduce((s, c) => s + c.w, 0);
        return { startX: Math.max(0, (1 - sum) / 2), cells };
      }

      // cropped frames share whatever width the pinned ones leave over
      let pinnedSum = 0;
      for (const i of items) if (!i.crop) pinnedSum += pinnedW(i);
      const freeTotal = Math.max(0, 1 - pinnedSum);
      const sumFreeW = free.reduce((s, i) => s + i.weight, 0) || 1;
      const cells = items.map(i => i.crop
        ? { item: i, w: freeTotal * (i.weight / sumFreeW) }
        : { item: i, w: pinnedW(i) });
      return { startX: 0, cells };
    }

    const lockedW = new Map();
    let lockedSum = 0;
    for (const i of items) {
      if (i.locked) {
        const w = i.lockAR * hr / CAR;
        lockedW.set(i, w);
        lockedSum += w;
      }
    }
    const free = items.filter(i => !i.locked);

    if (!free.length) {
      // all locked — centre the group, leftover paper shows
      return {
        startX: Math.max(0, (1 - lockedSum) / 2),
        cells: items.map(i => ({ item: i, w: lockedW.get(i) }))
      };
    }

    const freeTotal = Math.max(0, 1 - lockedSum);
    const sumFreeW = free.reduce((s, i) => s + i.weight, 0) || 1;
    const cells = items.map(i => i.locked
      ? { item: i, w: lockedW.get(i) }
      : { item: i, w: freeTotal * (i.weight / sumFreeW) });
    return { startX: 0, cells };
  }

  function fractions() {
    const rows = state.rows;
    if (!rows.length) return [];
    const { h, T } = heightFractions();
    const out = [];
    let y = state.whitespace ? Math.max(0, (1 - T) / 2) : 0;
    for (let r = 0; r < rows.length; r++) {
      const { startX, cells } = rowCells(rows[r], h[r]);
      let x = startX;
      for (const c of cells) {
        out.push({ item: c.item, row: rows[r], x, y, w: c.w, h: h[r] });
        x += c.w;
      }
      y += h[r];
    }
    return out;
  }

  function layout(animate) {
    const frs = fractions();
    const cw = canvas.clientWidth || 1280;
    const ch = canvas.clientHeight || 720;
    frs.forEach((f, i) => {
      const el = f.item.el;
      el.style.left = (f.x * 100) + '%';
      el.style.top = (f.y * 100) + '%';
      el.style.width = (f.w * 100) + '%';
      el.style.height = (f.h * 100) + '%';
      el.style.setProperty('--cw', (f.w * cw).toFixed(1) + 'px');
      el.style.setProperty('--ch', (f.h * ch).toFixed(1) + 'px');
      f.item._w = f.w;
      f.item._h = f.h;
      f.item.tag.textContent = pad(i + 1);
    });
    updateSelection();
    updateHUD();
    if (animate) {
      canvas.classList.add('animate');
      clearTimeout(layout._t);
      layout._t = setTimeout(() => canvas.classList.remove('animate'), 340);
    }
  }

  function rebuildDefault(clearLocks) {
    state.rows = [];
    if (clearLocks) {
      for (const it of state.items) {
        it.locked = false;
        it.lockAR = 0;
      }
    }
    const n = state.items.length;
    if (!n) return;
    const cols = Math.min(n, Math.max(1, Math.round(Math.sqrt(n * 4 / 3))));
    const rowCount = Math.ceil(n / cols);
    const sizes = new Array(rowCount).fill(Math.floor(n / rowCount));
    const rem = n - sizes.reduce((s, v) => s + v, 0);
    for (let i = 0; i < rem; i++) sizes[i]++;
    let k = 0;
    for (const size of sizes) {
      const items = state.items.slice(k, k + size);
      items.forEach(it => { it.weight = 1; });
      state.rows.push({ weight: 1, items });
      k += size;
    }
    state.userModified = false;
  }

  /* ---------------------------------------------------------
     Items
     --------------------------------------------------------- */

  function addItem(img, name) {
    const item = {
      id: ++state.seq,
      img,
      name: name || 'image',
      weight: 1,
      locked: false,
      lockAR: 0,
      rot: 0,
      crop: false,
      ar: (img.naturalWidth && img.naturalHeight)
        ? img.naturalWidth / img.naturalHeight
        : 1,
      _w: 0,
      _h: 0
    };

    const el = document.createElement('div');
    el.className = 'cell enter';
    el.dataset.id = String(item.id);
    el.tabIndex = 0;
    el.setAttribute('role', 'button');
    el.setAttribute('aria-label', 'Image: ' + item.name);

    const tag = document.createElement('div');
    tag.className = 'tag';

    const lockBtn = document.createElement('button');
    lockBtn.type = 'button';
    lockBtn.className = 'lockbtn';
    lockBtn.title = 'Lock / unlock proportions';
    lockBtn.setAttribute('aria-label', 'Lock / unlock proportions');
    lockBtn.setAttribute('aria-pressed', 'false');
    lockBtn.innerHTML =
      '<svg class="ico-open" viewBox="0 0 24 24" aria-hidden="true">' +
      '<rect x="4" y="11" width="16" height="10" rx="1"/>' +
      '<path d="M8 11V7a4 4 0 0 1 7.5-1.8"/></svg>' +
      '<svg class="ico-closed" viewBox="0 0 24 24" aria-hidden="true">' +
      '<rect x="4" y="11" width="16" height="10" rx="1"/>' +
      '<path d="M8 11V7a4 4 0 0 1 8 0v4"/></svg>';
    lockBtn.addEventListener('pointerdown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
    });
    lockBtn.addEventListener('click', ev => {
      ev.stopPropagation();
      toggleLock(item);
    });

    const rotBtn = document.createElement('button');
    rotBtn.type = 'button';
    rotBtn.className = 'rotbtn';
    rotBtn.title = 'Rotate 90°';
    rotBtn.setAttribute('aria-label', 'Rotate image 90 degrees');
    rotBtn.innerHTML =
      '<svg viewBox="0 0 24 24" aria-hidden="true">' +
      '<polyline points="23 4 23 10 17 10"/>' +
      '<path d="M20.49 15a9 9 0 1 1-2.12-9.36L23 10"/></svg>';
    rotBtn.addEventListener('pointerdown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
    });
    rotBtn.addEventListener('click', ev => {
      ev.stopPropagation();
      rotateItem(item);
    });

    const cropBtn = document.createElement('button');
    cropBtn.type = 'button';
    cropBtn.className = 'cropbtn';
    cropBtn.title = 'Crop / free proportions';
    cropBtn.setAttribute('aria-label', 'Crop image and free its proportions');
    cropBtn.setAttribute('aria-pressed', 'false');
    cropBtn.innerHTML =
      '<svg viewBox="0 0 24 24" aria-hidden="true">' +
      '<path d="M6.13 1L6 16a2 2 0 0 0 2 2h15"/>' +
      '<path d="M1 6.13L16 6a2 2 0 0 1 2 2v15"/></svg>';
    cropBtn.addEventListener('pointerdown', ev => {
      ev.stopPropagation();
      ev.preventDefault();
    });
    cropBtn.addEventListener('click', ev => {
      ev.stopPropagation();
      toggleCrop(item);
    });

    const handles = document.createElement('div');
    handles.className = 'handles';
    for (const d of DIRS) {
      const h = document.createElement('i');
      h.className = 'h ' + d;
      h.dataset.dir = d;
      handles.appendChild(h);
    }

    const clip = document.createElement('div');
    clip.className = 'clip';
    clip.appendChild(img);

    img.draggable = false;
    img.alt = item.name;
    el.append(clip, tag, lockBtn, rotBtn, cropBtn, handles);
    el.dataset.r = '0';
    item.el = el;
    item.tag = tag;
    item.lockBtn = lockBtn;
    item.cropBtn = cropBtn;
    canvas.appendChild(el);
    setTimeout(() => el.classList.remove('enter'), 420);

    state.items.push(item);

    if (!state.userModified) {
      rebuildDefault(false);
    } else {
      let target = null;
      for (const r of state.rows) {
        if (!target || r.items.length < target.items.length) target = r;
      }
      if (!target) {
        const meanRow = state.rows.length
          ? state.rows.reduce((s, r) => s + r.weight, 0) / state.rows.length
          : 1;
        target = { weight: meanRow, items: [] };
        state.rows.push(target);
        item.weight = 1;
        target.items.push(item);
      } else {
        const mean = target.items.length
          ? target.items.reduce((s, i) => s + i.weight, 0) / target.items.length
          : 1;
        item.weight = mean;
        target.items.push(item);
      }
    }

    layout(true);
  }

  function loadImage(src) {
    return new Promise((resolve, reject) => {
      const im = new Image();
      im.onload = () => resolve(im);
      im.onerror = reject;
      im.src = src;
    });
  }

  async function addFromSrc(src, name) {
    try {
      const img = await loadImage(src);
      addItem(img, name);
    } catch {
      toast('COULD NOT LOAD IMAGE');
    }
  }

  function handleFiles(list) {
    const files = Array.from(list || []).filter(f => f.type && f.type.startsWith('image/'));
    if (!files.length) { toast('NO IMAGE FILES FOUND'); return; }
    toast('ADDING ' + files.length + ' IMAGE' + (files.length > 1 ? 'S' : '') + '…');
    for (const f of files) addFromSrc(URL.createObjectURL(f), f.name);
  }

  function removeItem(item) {
    const row = rowOf(item);
    if (row) {
      row.items.splice(row.items.indexOf(item), 1);
      if (!row.items.length) state.rows.splice(state.rows.indexOf(row), 1);
    }
    state.items.splice(state.items.indexOf(item), 1);
    item.el.remove();
    if (state.selected === item) state.selected = null;
    if (!state.userModified) rebuildDefault(false);
    layout(true);
  }

  function swap(a, b) {
    const ra = rowOf(a);
    const rb = rowOf(b);
    const ia = ra.items.indexOf(a);
    const ib = rb.items.indexOf(b);
    const wa = a.weight;
    const wb = b.weight;
    ra.items[ia] = b;
    rb.items[ib] = a;
    a.weight = wb;   // a takes b's slot size
    b.weight = wa;   // b takes a's slot size
  }

  /* ---------------------------------------------------------
     Lock
     --------------------------------------------------------- */

  function toggleLock(item) {
    item.locked = !item.locked;
    if (item.locked) {
      const w = item._w || 0;
      const h = item._h || 0;
      item.lockAR = (h > 1e-6 && w > 1e-6) ? (w / h) * CAR : dispAR(item);
      toast('PROPORTIONS LOCKED — THIS FRAME HOLDS ITS SHAPE');
    } else {
      toast('PROPORTIONS UNLOCKED');
    }
    state.userModified = true;
    select(item);
    layout(true);
  }

  function rotateItem(item) {
    item.rot = ((item.rot || 0) + 90) % 360;
    item.el.dataset.r = String(item.rot);
    toast('ROTATED ' + item.rot + '°');
    select(item);
    layout(true);
  }

  function toggleCrop(item) {
    item.crop = !item.crop;
    toast(item.crop
      ? 'CROP ON — DRAG HANDLES TO RESHAPE, IMAGE CROPS TO FILL'
      : 'CROP OFF — BACK TO ORIGINAL PROPORTIONS');
    state.userModified = true;
    select(item);
    layout(true);
  }

  /* ---------------------------------------------------------
     Selection + HUD
     --------------------------------------------------------- */

  function select(item) {
    state.selected = item || null;
    updateSelection();
  }

  function updateSelection() {
    const sel = state.selected;
    for (const it of state.items) {
      it.el.classList.toggle('selected', it === sel);
      it.el.classList.toggle('locked', !!it.locked);
      it.el.classList.toggle('crop', !!it.crop);
      if (it.lockBtn) it.lockBtn.setAttribute('aria-pressed', it.locked ? 'true' : 'false');
      if (it.cropBtn) it.cropBtn.setAttribute('aria-pressed', it.crop ? 'true' : 'false');
    }
    if (!sel) return;

    const row = rowOf(sel);
    let canX;
    let canY;
    if (state.whitespace) {
      // row height only moves when there is more than one row; a cropped
      // frame reshapes by trading width with other cropped frames, or by
      // borrowing width from its row when pinned neighbours exist
      let pinnedAR = 0;
      let cropN = 0;
      for (const i of row.items) {
        if (i.crop) cropN++;
        else pinnedAR += dispAR(i);
      }
      if (sel.crop) {
        canX = cropN > 1 || (pinnedAR > 1e-6 && state.rows.length > 1);
        canY = state.rows.length > 1;
      } else {
        canX = state.rows.length > 1;
        canY = state.rows.length > 1;
      }
    } else if (sel.locked) {
      canX = state.rows.length > 1 || row.items.length > 1;
      canY = state.rows.length > 1 || row.items.length > 1;
    } else {
      canX = row.items.length > 1;
      canY = state.rows.length > 1;
    }

    sel.el.querySelectorAll('.h').forEach(h => {
      const d = h.dataset.dir;
      const usesX = d.includes('e') || d.includes('w');
      const usesY = d.includes('n') || d.includes('s');
      const ok = (usesX && canX) || (usesY && canY);
      h.classList.toggle('off', !ok);
    });
  }

  function updateHUD() {
    hudImages.textContent = pad(state.items.length);
    hudRows.textContent = pad(state.rows.length);
    hudLocked.textContent = pad(state.items.filter(i => i.locked).length);
    if (state.selected) {
      const s = state.selected;
      const flags = [];
      if (s.locked) flags.push('LOCKED');
      if (s.crop && state.whitespace) flags.push('CROP');
      hudSelected.textContent = s.name + (flags.length ? ' · ' + flags.join(' · ') : '');
      hudSelected.title = s.name;
    } else {
      hudSelected.textContent = '—';
      hudSelected.title = '';
    }
    emptyState.hidden = state.items.length > 0;
  }

  /* ---------------------------------------------------------
     Gestures: resize (8 handles) + drag-to-swap
     --------------------------------------------------------- */

  let gesture = null;

  canvas.addEventListener('pointerdown', e => {
    if (e.button !== undefined && e.button !== 0) return;
    const handle = e.target.closest('.h');
    const cell = e.target.closest('.cell');
    if (handle && cell) {
      const item = state.items.find(i => i.id === Number(cell.dataset.id));
      if (!item || handle.classList.contains('off')) return;
      e.preventDefault();
      e.stopPropagation();
      select(item);
      beginResize(item, handle.dataset.dir, e);
    } else if (cell) {
      const item = state.items.find(i => i.id === Number(cell.dataset.id));
      if (!item) return;
      select(item);
      beginMove(item, e);
    } else {
      select(null);
    }
  });

  canvas.addEventListener('keydown', e => {
    if (e.key !== 'Enter' && e.key !== ' ') return;
    const cell = e.target.closest && e.target.closest('.cell');
    if (!cell) return;
    e.preventDefault();
    const item = state.items.find(i => i.id === Number(cell.dataset.id));
    if (item) select(item);
  });

  function beginResize(item, dir, e) {
    const cr = canvas.getBoundingClientRect();
    const f = fractions().find(x => x.item === item);
    const row = rowOf(item);
    canvas.classList.remove('animate');

    const totalH0 = state.rows.reduce((s, r) => s + r.weight, 0) || 1;
    const wsMode = state.whitespace;
    let lockedSum0 = 0;
    let freeSum0 = 0;
    let freeCount = 0;
    let pinnedAR0 = 0;
    for (const i of row.items) {
      const pinned = wsMode ? !i.crop : i.locked;
      if (pinned) {
        const ar = wsMode ? dispAR(i) : i.lockAR;
        lockedSum0 += ar * f.h / CAR;
        if (wsMode) pinnedAR0 += ar;
      } else {
        freeSum0 += i.weight;
        freeCount++;
      }
    }

    gesture = {
      type: 'resize',
      dir,
      x0: e.clientX,
      y0: e.clientY,
      cw: Math.max(cr.width, 1),
      ch: Math.max(cr.height, 1),
      w0: f.w,
      h0: f.h,
      weight0: item.weight,
      sumW0: row.items.reduce((s, i) => s + i.weight, 0),
      lockedSum0,
      freeSum0,
      freeCount,
      pinnedAR0,
      rowWeight0: row.weight,
      totalH0,
      count: row.items.length,
      rowCount: state.rows.length,
      minFX: MIN / Math.max(cr.width, 1),
      minFY: MIN / Math.max(cr.height, 1),
      lockAR: item.lockAR || dispAR(item),
      locked: item.locked,
      ws: wsMode,
      crop: wsMode && !!item.crop,
      row,
      item
    };
    window.addEventListener('pointermove', onResizeMove);
  }

  function onResizeMove(e) {
    const g = gesture;
    if (!g || g.type !== 'resize') return;

    const rawX = (e.clientX - g.x0) / g.cw;
    const rawY = (e.clientY - g.y0) / g.ch;
    const horiz = g.dir.includes('e') || g.dir.includes('w');
    const vert = g.dir.includes('n') || g.dir.includes('s');
    const dw = horiz ? (g.dir.includes('e') ? rawX : -rawX) : 0;
    const dh = vert ? (g.dir.includes('s') ? rawY : -rawY) : 0;

    const maxHFrac = Math.max(g.minFY, 1 - g.minFY * (g.rowCount - 1));
    const maxWFrac = Math.max(g.minFX, 1 - g.minFX * (g.count - 1));
    const setRowH = hf => {
      g.row.weight = clamp(hf, g.minFY, maxHFrac) * g.totalH0;
    };

    if (g.ws && !g.crop) {
      // white-space mode: dragging scales the whole row, all
      // images keep their original proportions
      const sw = g.w0 > 1e-6 ? (g.w0 + dw) / g.w0 : 1;
      const sh = g.h0 > 1e-6 ? (g.h0 + dh) / g.h0 : 1;
      const s = (horiz && vert) ? (sw + sh) / 2 : (horiz ? sw : sh);
      setRowH(g.h0 * s);
    } else if (g.ws) {
      // white-space + crop: reshape this frame only
      let targetH = null;
      if (horiz && g.freeCount > 1) {
        // trade width with the other cropped frames in the same row
        const freeTotal0 = Math.max(1e-6, 1 - g.lockedSum0);
        const maxShareW = Math.max(g.minFX, freeTotal0 - g.minFX * (g.freeCount - 1));
        const newW = clamp(g.w0 + dw, g.minFX, maxShareW);
        const others = Math.max(1e-6, g.freeSum0 - g.weight0);
        const t = clamp(newW / freeTotal0, 1e-3, 1 - 1e-3);
        g.item.weight = (t / (1 - t)) * others;
      } else if (horiz && g.pinnedAR0 > 1e-6) {
        // widen by shrinking the row — pinned neighbours keep their aspect
        const newW = clamp(g.w0 + dw, g.minFX, maxWFrac);
        targetH = (1 - newW) * CAR / g.pinnedAR0;
      }
      if (vert) targetH = (targetH === null ? g.h0 : targetH) + dh;
      if (targetH !== null) setRowH(targetH);
    } else if (g.locked) {
      // locked frame: any drag resizes it proportionally
      if (horiz && vert) {
        const sw = g.w0 > 1e-6 ? (g.w0 + dw) / g.w0 : 1;
        const sh = g.h0 > 1e-6 ? (g.h0 + dh) / g.h0 : 1;
        setRowH(g.h0 * (sw + sh) / 2);
      } else if (horiz) {
        const newW = clamp(g.w0 + dw, g.minFX, maxWFrac);
        const newH = newW * CAR / Math.max(g.lockAR, 1e-6);
        setRowH(newH);
      } else {
        setRowH(g.h0 + dh);
      }
    } else {
      // free frame in auto-fit mode
      if (horiz) {
        const newW = clamp(g.w0 + dw, g.minFX, maxWFrac);
        if (g.freeCount > 0 && g.lockedSum0 < 1 - 1e-6) {
          const freeTotal0 = Math.max(1e-6, 1 - g.lockedSum0);
          g.item.weight = (newW / freeTotal0) * g.freeSum0;
        } else {
          g.item.weight = newW * g.sumW0;
        }
      }
      if (vert) setRowH(g.h0 + dh);
    }

    state.userModified = true;
    layout();
  }

  function beginMove(item, e) {
    gesture = {
      type: 'move',
      item,
      x0: e.clientX,
      y0: e.clientY,
      active: false,
      cell: item.el,
      cr: canvas.getBoundingClientRect()
    };
    window.addEventListener('pointermove', onMoveMove);
  }

  function onMoveMove(e) {
    const g = gesture;
    if (!g || g.type !== 'move') return;

    if (!g.active) {
      if (Math.hypot(e.clientX - g.x0, e.clientY - g.y0) < 5) return;
      g.active = true;
      g.cell.classList.add('dragging');
      canvas.classList.remove('animate');
    }

    const px = (e.clientX - g.cr.left) / g.cr.width;
    const py = (e.clientY - g.cr.top) / g.cr.height;
    if (px < 0 || px > 1 || py < 0 || py > 1) return;

    for (const f of fractions()) {
      if (f.item === g.item) continue;
      if (px >= f.x && px < f.x + f.w && py >= f.y && py < f.y + f.h) {
        swap(g.item, f.item);
        state.userModified = true;
        layout();
        break;
      }
    }
  }

  function endGesture() {
    window.removeEventListener('pointermove', onResizeMove);
    window.removeEventListener('pointermove', onMoveMove);
    if (gesture && gesture.cell) gesture.cell.classList.remove('dragging');
    gesture = null;
  }

  window.addEventListener('pointerup', endGesture);
  window.addEventListener('pointercancel', endGesture);

  /* ---------------------------------------------------------
     Import: upload, paste, drop
     --------------------------------------------------------- */

  document.getElementById('uploadBtn').addEventListener('click', () => fileInput.click());
  document.getElementById('emptyBtn').addEventListener('click', () => fileInput.click());

  fileInput.addEventListener('change', () => {
    handleFiles(fileInput.files);
    fileInput.value = '';
  });

  window.addEventListener('paste', e => {
    const items = e.clipboardData && e.clipboardData.items;
    if (!items) return;
    const files = [];
    for (const it of items) {
      if (it.type && it.type.startsWith('image/')) {
        const f = it.getAsFile();
        if (f) files.push(f);
      }
    }
    if (files.length) {
      e.preventDefault();
      handleFiles(files);
    }
  });

  document.getElementById('pasteBtn').addEventListener('click', async () => {
    if (!navigator.clipboard || !navigator.clipboard.read) {
      toast('PRESS ⌘V / CTRL+V ANYWHERE');
      return;
    }
    try {
      const boards = await navigator.clipboard.read();
      const files = [];
      for (const b of boards) {
        for (const type of b.types) {
          if (type.startsWith('image/')) {
            const blob = await b.getType(type);
            files.push(new File([blob], 'pasted-image.png', { type }));
          }
        }
      }
      if (files.length) handleFiles(files);
      else toast('NO IMAGE IN CLIPBOARD');
    } catch {
      toast('PRESS ⌘V / CTRL+V ANYWHERE');
    }
  });

  let dragDepth = 0;
  window.addEventListener('dragenter', e => {
    e.preventDefault();
    dragDepth++;
    canvas.classList.add('drop-hot');
  });
  window.addEventListener('dragover', e => e.preventDefault());
  window.addEventListener('dragleave', e => {
    e.preventDefault();
    dragDepth = Math.max(0, dragDepth - 1);
    if (!dragDepth) canvas.classList.remove('drop-hot');
  });
  window.addEventListener('drop', e => {
    e.preventDefault();
    dragDepth = 0;
    canvas.classList.remove('drop-hot');
    if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files.length) {
      handleFiles(e.dataTransfer.files);
    }
  });

  /* ---------------------------------------------------------
     Toolbar actions
     --------------------------------------------------------- */

  document.getElementById('deleteBtn').addEventListener('click', () => {
    if (state.selected) removeItem(state.selected);
    else toast('SELECT AN IMAGE FIRST');
  });

  document.getElementById('resetBtn').addEventListener('click', () => {
    if (!state.items.length) { toast('NO IMAGES YET'); return; }
    rebuildDefault(true);
    layout(true);
    toast('GRID RESET — EQUAL SIZES, LOCKS CLEARED');
  });

  gapRange.addEventListener('input', () => {
    state.gap = Number(gapRange.value);
    gapVal.textContent = state.gap + 'PX';
    canvas.style.setProperty('--gh', (state.gap / 2) + 'px');
  });

  wsCheck.addEventListener('change', () => {
    state.whitespace = wsCheck.checked;
    canvas.classList.toggle('ws', state.whitespace);
    modeLabel.textContent = state.whitespace
      ? 'MODE — WHITE SPACE (ORIGINAL PROPORTIONS, NO CROP)'
      : 'MODE — AUTO-FIT (CROP TO FILL)';
    if (state.whitespace) {
      state.userModified = true;
      toast('WHITE SPACE ON — ORIGINAL PROPORTIONS KEPT, NOTHING CROPPED');
    } else {
      toast('AUTO-FIT ON — IMAGES FILL THEIR FRAMES');
    }
    layout(true);
  });

  /* ---------------------------------------------------------
     Export
     --------------------------------------------------------- */

  document.getElementById('downloadBtn').addEventListener('click', exportPNG);

  function exportPNG() {
    if (!state.items.length) { toast('ADD IMAGES FIRST'); return; }

    const c = document.createElement('canvas');
    c.width = EXPORT_W;
    c.height = EXPORT_H;
    const ctx = c.getContext('2d');
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, EXPORT_W, EXPORT_H);

    const displayW = canvas.clientWidth || EXPORT_W;
    const gapOut = state.gap * (EXPORT_W / displayW);

    for (const f of fractions()) {
      const x = f.x * EXPORT_W + gapOut / 2;
      const y = f.y * EXPORT_H + gapOut / 2;
      const w = f.w * EXPORT_W - gapOut;
      const h = f.h * EXPORT_H - gapOut;
      if (w < 1 || h < 1) continue;

      const im = f.item.img;
      const iw = im.naturalWidth || im.width;
      const ih = im.naturalHeight || im.height;
      if (!iw || !ih) continue;

      const deg = (f.item.rot || 0) % 360;
      const swap = deg % 180 === 90;
      const bw = swap ? h : w;
      const bh = swap ? w : h;

      ctx.save();
      ctx.translate(x + w / 2, y + h / 2);
      if (deg) ctx.rotate(deg * Math.PI / 180);

      if (state.whitespace && !f.item.crop) {
        // pinned — proportions already match, draw whole image, no crop
        ctx.drawImage(im, -bw / 2, -bh / 2, bw, bh);
      } else {
        // cover-crop, matching CSS object-fit: cover
        const targetAR = bw / bh;
        const imgAR = iw / ih;
        let sx = 0, sy = 0, sw = iw, sh = ih;
        if (imgAR > targetAR) {
          sh = ih;
          sw = ih * targetAR;
          sx = (iw - sw) / 2;
        } else {
          sw = iw;
          sh = iw / targetAR;
          sy = (ih - sh) / 2;
        }
        ctx.drawImage(im, sx, sy, sw, sh, -bw / 2, -bh / 2, bw, bh);
      }
      ctx.restore();
    }

    const a = document.createElement('a');
    a.download = 'collage-crew-' + state.items.length + 'imgs.png';
    a.href = c.toDataURL('image/png');
    a.click();
    toast('EXPORTED ' + EXPORT_W + '×' + EXPORT_H + ' PNG');
  }

  /* ---------------------------------------------------------
     Keyboard
     --------------------------------------------------------- */

  window.addEventListener('keydown', e => {
    const tag = (document.activeElement && document.activeElement.tagName) || '';
    if (tag === 'INPUT' || tag === 'TEXTAREA') return;
    if (e.key === 'Escape') select(null);
    if ((e.key === 'Delete' || e.key === 'Backspace') && state.selected) {
      e.preventDefault();
      removeItem(state.selected);
    }
  });

  /* ---------------------------------------------------------
     Toast
     --------------------------------------------------------- */

  function toast(msg) {
    const t = document.createElement('div');
    t.className = 'toast';
    t.textContent = msg;
    while (toastWrap.children.length >= 3) toastWrap.firstChild.remove();
    toastWrap.appendChild(t);
    setTimeout(() => {
      t.classList.add('out');
      setTimeout(() => t.remove(), 300);
    }, 2400);
  }

  /* ---------------------------------------------------------
     Boot
     --------------------------------------------------------- */

  window.addEventListener('resize', () => { if (!gesture) layout(); });
  layout();
})();
