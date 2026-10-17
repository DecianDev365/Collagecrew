(() => {
  'use strict';

  /* ---------------------------------------------------------
     COLLAGE CREW engine
     Layout model: justified rows on a 16:9 canvas.
     - rows partition canvas height by weight
     - items partition row width by weight
     - resizing one item renormalises its row / the other rows,
       so "corresponding" neighbours shrink or grow automatically
     --------------------------------------------------------- */

  const canvas = document.getElementById('canvas');
  const emptyState = document.getElementById('empty');
  const fileInput = document.getElementById('fileInput');
  const toastWrap = document.getElementById('toast');
  const hudImages = document.getElementById('hudImages');
  const hudRows = document.getElementById('hudRows');
  const hudSelected = document.getElementById('hudSelected');
  const gapRange = document.getElementById('gapRange');
  const gapVal = document.getElementById('gapVal');

  const DIRS = ['nw', 'n', 'ne', 'e', 'se', 's', 'sw', 'w'];
  const MIN = 44;          // min cell size in display px
  const EXPORT_W = 3200;
  const EXPORT_H = 1800;

  const state = {
    items: [],             // flat list, insertion order
    rows: [],              // [{ weight, items: [item, ...] }]
    selected: null,
    userModified: false,
    gap: 0,
    seq: 0
  };

  const pad = n => String(n).padStart(2, '0');
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  const rowOf = item => state.rows.find(r => r.items.includes(item));

  /* ---------------------------------------------------------
     Layout maths
     --------------------------------------------------------- */

  function fractions() {
    const out = [];
    const totalH = state.rows.reduce((s, r) => s + r.weight, 0) || 1;
    let y = 0;
    for (const r of state.rows) {
      const h = r.weight / totalH;
      const sumW = r.items.reduce((s, i) => s + i.weight, 0) || 1;
      let x = 0;
      for (const it of r.items) {
        const w = it.weight / sumW;
        out.push({ item: it, row: r, x, y, w, h });
        x += w;
      }
      y += h;
    }
    return out;
  }

  function layout(animate) {
    const frs = fractions();
    frs.forEach((f, i) => {
      const el = f.item.el;
      el.style.left = (f.x * 100) + '%';
      el.style.top = (f.y * 100) + '%';
      el.style.width = (f.w * 100) + '%';
      el.style.height = (f.h * 100) + '%';
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

  function rebuildDefault() {
    state.rows = [];
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
    const item = { id: ++state.seq, img, name: name || 'image', weight: 1 };

    const el = document.createElement('div');
    el.className = 'cell enter';
    el.dataset.id = String(item.id);

    const tag = document.createElement('div');
    tag.className = 'tag';

    const handles = document.createElement('div');
    handles.className = 'handles';
    for (const d of DIRS) {
      const h = document.createElement('i');
      h.className = 'h ' + d;
      h.dataset.dir = d;
      handles.appendChild(h);
    }

    img.draggable = false;
    img.alt = item.name;
    el.append(img, tag, handles);
    item.el = el;
    item.tag = tag;
    canvas.appendChild(el);
    setTimeout(() => el.classList.remove('enter'), 420);

    state.items.push(item);

    if (!state.userModified) {
      rebuildDefault();
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
        const others = target.items;
        const mean = others.length
          ? others.reduce((s, i) => s + i.weight, 0) / others.length
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
    if (!state.userModified) rebuildDefault();
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
    }
    if (!sel) return;

    const row = rowOf(sel);
    const canX = row.items.length > 1;
    const canY = state.rows.length > 1;
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
    if (state.selected) {
      hudSelected.textContent = state.selected.name;
      hudSelected.title = state.selected.name;
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

  function beginResize(item, dir, e) {
    const cr = canvas.getBoundingClientRect();
    const f = fractions().find(x => x.item === item);
    const row = rowOf(item);
    canvas.classList.remove('animate');
    gesture = {
      type: 'resize',
      dir,
      x0: e.clientX,
      y0: e.clientY,
      w0: f.w * cr.width,
      h0: f.h * cr.height,
      cw: cr.width,
      ch: cr.height,
      weight0: item.weight,
      sumW0: row.items.reduce((s, i) => s + i.weight, 0),
      rowWeight0: row.weight,
      totalH0: state.rows.reduce((s, r) => s + r.weight, 0),
      count: row.items.length,
      rowCount: state.rows.length,
      row,
      item
    };
    window.addEventListener('pointermove', onResizeMove);
  }

  function onResizeMove(e) {
    const g = gesture;
    if (!g || g.type !== 'resize') return;
    const dx = e.clientX - g.x0;
    const dy = e.clientY - g.y0;
    const dir = g.dir;
    let changed = false;

    if (dir.includes('e') || dir.includes('w')) {
      const dw = dir.includes('e') ? dx : -dx;
      const maxW = g.cw - MIN * (g.count - 1);
      const newW = clamp(g.w0 + dw, MIN, Math.max(MIN, maxW));
      g.item.weight = (newW / g.cw) * g.sumW0;
      changed = true;
    }

    if (dir.includes('n') || dir.includes('s')) {
      const dh = dir.includes('s') ? dy : -dy;
      const maxH = g.ch - MIN * (g.rowCount - 1);
      const newH = clamp(g.h0 + dh, MIN, Math.max(MIN, maxH));
      g.row.weight = (newH / g.ch) * g.totalH0;
      changed = true;
    }

    if (changed) {
      state.userModified = true;
      layout();
    }
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
    rebuildDefault();
    layout(true);
    toast('GRID RESET — EQUAL SIZES');
  });

  gapRange.addEventListener('input', () => {
    state.gap = Number(gapRange.value);
    gapVal.textContent = state.gap + 'PX';
    canvas.style.setProperty('--gh', (state.gap / 2) + 'px');
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
      let x = f.x * EXPORT_W + gapOut / 2;
      let y = f.y * EXPORT_H + gapOut / 2;
      let w = f.w * EXPORT_W - gapOut;
      let h = f.h * EXPORT_H - gapOut;
      if (w < 1 || h < 1) continue;

      const im = f.item.img;
      const iw = im.naturalWidth || im.width;
      const ih = im.naturalHeight || im.height;
      if (!iw || !ih) continue;

      // cover-crop, matching CSS object-fit: cover
      const targetAR = w / h;
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
      ctx.drawImage(im, sx, sy, sw, sh, x, y, w, h);
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
