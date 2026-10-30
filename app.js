'use strict';
/* ===== Utilidades ===== */
const $ = i => document.getElementById(i), fx = (v, d = 4) => Number(v).toFixed(d + dx()), dx = () => Math.max(0, Math.min(6, parseInt($('p_dec').value) || 0)), ex = v => Number(v).toExponential(3);
const T = m => m[0].map((_, j) => m.map(r => r[j]));
const MM = (a, b) => { const t = T(b); return a.map(r => t.map(c => r.reduce((s, v, k) => s + v * c[k], 0))); };
const MV = (a, v) => a.map(r => r.reduce((s, x, k) => s + x * v[k], 0));
const dot = (a, b) => a.reduce((s, v, k) => s + v * b[k], 0);
function inv(m) {
  const n = m.length, sc = Math.max(...m.flat().map(Math.abs));
  const a = m.map((r, i) => [...r, ...Array.from({ length: n }, (_, j) => +(i === j))]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(a[r][c]) > Math.abs(a[p][c])) p = r;
    if (Math.abs(a[p][c]) < 1e-13 * sc) throw Error('Sistema singular: revise puntos fijos y observaciones.');
    [a[c], a[p]] = [a[p], a[c]];
    const d = a[c][c]; a[c] = a[c].map(v => v / d);
    for (let r = 0; r < n; r++) if (r !== c) { const f = a[r][c]; if (f) a[r] = a[r].map((v, k) => v - f * a[c][k]); }
  }
  return a.map(r => r.slice(n));
}
/* Ajuste libre: restricciones interiores (pseudoinversa): Qxx = (N + B'B)^-1 - B'B */
function freeInv(N, B) {
  const BtB = MM(T(B), B);
  return inv(N.map((r, i) => r.map((v, j) => v + BtB[i][j]))).map((r, i) => r.map((v, j) => v - BtB[i][j]));
}
function datumB(A, xy, u) {
  const m = xy.length, cx = xy.reduce((s, q) => s + q[0], 0) / m, cy = xy.reduce((s, q) => s + q[1], 0) / m, ev = k => k % 2 === 0, pt = k => xy[k >> 1];
  const rows = [
    Array.from({ length: u }, (_, k) => +ev(k)), Array.from({ length: u }, (_, k) => +!ev(k)),
    Array.from({ length: u }, (_, k) => ev(k) ? -(pt(k)[1] - cy) : pt(k)[0] - cx),   /* rotación */
    Array.from({ length: u }, (_, k) => ev(k) ? pt(k)[0] - cx : pt(k)[1] - cy)];     /* escala */
  return rows.map(b => { const nb = Math.hypot(...b); return b.map(v => v / nb); })
    .filter(b => MV(A, b).every((v, i) => Math.abs(v) <= 1e-8 * Math.hypot(...A[i])));  /* solo los grados de libertad que las observaciones NO definen */
}
/* Chi-cuadrado: gamma incompleta + bisección */
function lg(x) {
  const c = [76.18009172947146, -86.50532032941677, 24.01409824083091, -1.231739572450155, 0.1208650973866179e-2, -0.5395239384953e-5];
  let y = x, t = x + 5.5; t -= (x + .5) * Math.log(t); let s = 1.000000000190015;
  for (const k of c) s += k / ++y;
  return -t + Math.log(2.5066282746310005 * s / x);
}
function gP(a, x) {
  if (x <= 0) return 0;
  const pre = Math.exp(-x + a * Math.log(x) - lg(a));
  if (x < a + 1) { let s = 1 / a, t = s; for (let n = 1; n < 500; n++) { t *= x / (a + n); s += t; if (Math.abs(t) < Math.abs(s) * 1e-15) break; } return s * pre; }
  let b = x + 1 - a, c = 1e300, d = 1 / b, h = d;
  for (let i = 1; i < 500; i++) {
    const an = -i * (i - a); b += 2; d = an * d + b; if (Math.abs(d) < 1e-300) d = 1e-300;
    c = b + an / c; if (Math.abs(c) < 1e-300) c = 1e-300; d = 1 / d; const dl = d * c; h *= dl; if (Math.abs(dl - 1) < 1e-15) break;
  }
  return 1 - pre * h;
}
function chi2q(p, k) { let lo = 0, hi = k + 10; while (gP(k / 2, hi / 2) < p) hi *= 2; for (let i = 0; i < 200; i++) { const m = (lo + hi) / 2; gP(k / 2, m / 2) < p ? lo = m : hi = m; } return (lo + hi) / 2; }
/* Lectura de TXT */
const normT = t => t.replace(/[\u2212\u2013\u2014\u2010\u2011\u2012]/g, '-').replace(/[\u00A0\u2007\u2009\u202F]/g, ' ').replace(/[\u200B\uFEFF]/g, '');
function parse(txt, nc, name) {
  const rows = [];
  txt.split(/\r?\n/).forEach((ln, i) => {
    ln = normT(ln).split('#')[0].trim(); if (!ln) return;
    const c = ln.split(/[\s,;]+/);
    if (c.length !== nc) throw Error(`${name}, línea ${i + 1}: se esperan ${nc} columnas.`);
    rows.push(c);
  });
  return rows;
}
const num = (s, name) => { const v = Number(s); if (!isFinite(v) || s === '') throw Error(`${name}: "${s}" no es un número válido.`); return v; };
/* Constructor de reporte (HTML + TXT) */
class Rep {
  constructor() {
    const e = s => s.replace(/[&<>]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c])), pn = $('p_nom').value.trim(), po = $('p_op').value.trim();
    const meta = new Date().toLocaleString() + (pn ? ' · Proyecto: ' + pn : '') + (po ? ' · Operador: ' + po : '');
    this.h = `<p class="hint">${e(meta)}</p>`; this.t = 'REPORTE DE AJUSTE POR MINIMOS CUADRADOS (METODO PARAMETRICO)\n' + meta + '\n';
  }
  cards(a) { this.h += '<div class="cards">' + a.map(([k, v]) => `<div class="k"><b>${v}</b><span>${k}</span></div>`).join('') + '</div>'; return this; }
  sec(title, hd, rows) {
    this.h += `<h3>${title}</h3><div class="tw"><table><thead><tr>${hd.map(x => `<th>${x}</th>`).join('')}</tr></thead><tbody>${rows.map(r => `<tr>${r.map(x => `<td>${x}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
    this.t += `\n${title}\n${'-'.repeat(90)}\n` + [hd, ...rows].map(r => r.map((x, i) => String(x).replace(/<[^>]+>/g, '')[i ? 'padStart' : 'padEnd'](i ? 16 : 22)).join('')).join('\n') + '\n';
    return this;
  }
  top(it) {
    const h = '<h3>Resumen de verificación</h3><ul class="chk">' + it.map(([ok, t]) => `<li class="${ok ? 'ok' : 'bad'}">${ok ? '✅' : '⚠️'} ${t}</li>`).join('') + '</ul>';
    this.h = h + this.h; const k = this.t.indexOf('\n', this.t.indexOf('\n') + 1) + 1;
    this.t = this.t.slice(0, k) + '\nRESUMEN DE VERIFICACION\n' + it.map(([ok, t]) => (ok ? '[OK] ' : '[!!] ') + t).join('\n') + '\n' + this.t.slice(k); return this;
  }
  note(s, cls) { this.h += `<p class="${cls || ''}">${s}</p>`; this.t += s.replace(/<[^>]+>/g, '') + '\n'; return this; }
}
const texts = {}, csvs = {};
function show(id, fn) {
  try { const r = fn(); texts[id] = r.t; csvs[id] = r.csv || ''; $(id).innerHTML = `<div class="card">${r.h}${r.extra || ''}</div>`; if (id === 'rr') enableZoom(); }
  catch (e) { $(id).innerHTML = `<div class="err">⚠ ${e.message}</div>`; }
}
const verdict = (ok, a, b) => `<span class="${ok ? 'ok' : 'bad'}">${ok ? a : b}</span>`;

/* ===== MÓDULO 1: NIVELACIÓN ===== */
function runNiv() {
  const s0 = +$('n_s0').value, al = +$('n_alfa').value, sk = +$('n_sk').value, al0 = +$('n_alfa0').value;
  const ob = parse($('n_obs').value, 4, 'nivelacion.txt').map(r => ({ d: r[0], h: r[1], dh: num(r[2], r[0] + '-' + r[1]), L: num(r[3], r[0] + '-' + r[1]) }));
  const fj = parse($('n_fix').value, 2, 'fijos_nivelacion.txt').map(r => [r[0], num(r[1], r[0])]);
  if (!ob.length) throw Error('No hay observaciones.');
  if (!fj.length) throw Error('Indique al menos un punto fijo.');
  if (ob.some(o => o.L <= 0)) throw Error('Las longitudes deben ser positivas.');
  if (ob.some(o => o.d === o.h)) throw Error('Hay un tramo con el mismo punto de salida y llegada.');
  const all = [...new Set([...ob.map(o => o.d), ...ob.map(o => o.h)])];
  fj.forEach(([n]) => { if (!all.includes(n)) throw Error('Punto fijo inexistente en la red: ' + n); });
  const H0 = {}, LD = {}; fj.forEach(([n, h]) => { H0[n] = h; LD[n] = 0; });
  const used = ob.map(() => false);
  const cola = fj.map(f_ => f_[0]);
  while (cola.length) {
    const k = cola.shift();
    ob.forEach((o, i) => {
      if (used[i]) return;
      if (o.d === k && !(o.h in H0)) { H0[o.h] = H0[o.d] + o.dh; LD[o.h] = LD[o.d] + o.L; used[i] = true; cola.push(o.h); }
      else if (o.h === k && !(o.d in H0)) { H0[o.d] = H0[o.h] - o.dh; LD[o.d] = LD[o.h] + o.L; used[i] = true; cola.push(o.d); }
    });
  }
  const lost = all.filter(p => !(p in H0));
  if (lost.length) throw Error('Puntos no conectados con ningún punto fijo: ' + lost.join(', '));
  const libre = $('n_libre').checked, inc = libre ? all.slice() : all.filter(p => !fj.some(f => f[0] === p)), u = inc.length, n = ob.length, f = n - u + (libre ? 1 : 0);
  if (!u) throw Error('La red no tiene puntos desconocidos.');
  if (f <= 0) throw Error(`Redundancia f = ${f}: no hay control estadístico.`);
  const A = ob.map(o => inc.map(p => (p === o.h) - (p === o.d)));
  const l = ob.map(o => (o.dh - (H0[o.h] - H0[o.d])) * 1000);
  const sg = ob.map(o => sk * Math.sqrt(o.L)), p = sg.map(s => s0 * s0 / (s * s));
  const PA = A.map((r, i) => r.map(v => v * p[i])), N = MM(T(A), PA), t = MV(T(PA), l);
  const Q = libre ? freeInv(N, [Array(u).fill(1 / Math.sqrt(u))]) : inv(N), x = MV(Q, t), v = A.map((r, i) => dot(r, x) - l[i]);
  const vPv = v.reduce((s, e, i) => s + p[i] * e * e, 0), s02 = vPv / f, Tc = vPv / (s0 * s0);
  const lo = chi2q(al / 2, f), hi = chi2q(1 - al / 2, f), cu = chi2q(1 - al, f), ok = Tc >= lo && Tc <= hi;
  const AQ = MM(A, Q), sL = AQ.map((r, i) => Math.sqrt(s02 * dot(r, A[i])));
  const im = v.reduce((m, e, i) => Math.abs(e) > Math.abs(v[m]) ? i : m, 0);
  const R = new Rep().cards([['Observaciones n', n], ['Incógnitas u', u], ['Redundancia f', f], ['σ₀ a posteriori', fx(Math.sqrt(s02), 4)], ['T = v′Pv/σ₀²', fx(Tc, 3)]]);
  R.sec('Alturas ajustadas', ['Punto', 'Tipo', 'H aprox [m]', 'Corrección [mm]', 'H ajustada [m]', 'σ [mm]'],
    [...(libre ? [] : fj).map(([n_, h]) => [n_, 'FIJO', fx(h), '0.000', fx(h), '0.000']), ...inc.map((n_, i) => [n_, 'LIBRE', fx(H0[n_]), fx(x[i], 3), fx(H0[n_] + x[i] / 1000), fx(Math.sqrt(s02 * Q[i][i]), 3)])]);
  R.sec('Observaciones y residuos', ['Tramo', 'L [km]', 'σ [mm]', 'peso', 'dh obs [m]', 'v [mm]', 'dh ajust [m]', 'σ ajust [mm]'],
    ob.map((o, i) => [`${i + 1}: ${o.d}-${o.h}`, fx(o.L, 3), fx(sg[i], 3), fx(p[i], 5), fx(o.dh), fx(v[i], 3), fx(o.dh + v[i] / 1000), fx(sL[i], 3)]));
  const qv = ob.map((_, i) => 1 / p[i] - dot(AQ[i], A[i])), rv = qv.map((q, i) => q * p[i]), wv = v.map((e, i) => e / Math.sqrt(s0 * s0 * qv[i])), wl = Math.sqrt(chi2q(1 - al0, 1)), bd = wv.map(e => Math.abs(e) > wl);
  R.sec('Ecuaciones de observación: A y l [mm]', ['Tramo', ...inc, 'l [mm]'], ob.map((o, i) => [`${i + 1}: ${o.d}-${o.h}`, ...A[i], fx(l[i], 3)]));
  R.sec(`Test de Baarda (límite z = ${fx(wl, 4)}, α₀ = ${al0})`, ['Tramo', 'v [mm]', 'peso p', 'r_i', 'w', 'Resultado'], ob.map((o, i) => [`${i + 1}: ${o.d}-${o.h}`, fx(v[i], 3), fx(p[i], 5), fx(rv[i], 4), fx(wv[i], 4), bd[i] ? '<b style="color:#b42318">ERROR GROSERO</b>' : 'ok']));
  R.note(`Σ r_i = ${fx(rv.reduce((a, b) => a + b, 0), 4)} (debe ser ${f}). Menor r_i: tramo ${rv.indexOf(Math.min(...rv)) + 1} (${fx(Math.min(...rv), 4)})${Math.min(...rv) < 0.3 ? '; con r_i < 0.3 el control es débil.' : '.'}`, '');
  R.sec('Matriz N = A′PA [mm⁻²]', ['', ...inc], N.map((r, i) => [inc[i], ...r.map(e => fx(e, 5))]));
  R.sec('Cofactor Qxx = N⁻¹ [mm²]', ['', ...inc], Q.map((r, i) => [inc[i], ...r.map(e => fx(e, 5))]));
  R.note(`<b>Test χ² bilateral (α=${al}, ${f} g.l.):</b> T = ${fx(Tc, 4)} · intervalo [${fx(lo, 4)} ; ${fx(hi, 4)}] → ` + verdict(ok, 'PASA', Tc < lo ? 'NO PASA (T bajo: precisiones a priori pesimistas)' : 'NO PASA (T alto: errores en datos o σ optimista)'), '');
  R.note(`<b>Prueba unilateral:</b> crítico ${fx(cu, 4)} → ` + verdict(Tc <= cu, 'SE ACEPTA el modelo', 'SE RECHAZA: revisar observaciones'), '');
  R.note(`Mayor residuo: tramo ${im + 1} (${ob[im].d}-${ob[im].h}), |v| = ${fx(Math.abs(v[im]), 3)} mm. Es un indicio a investigar, no una prueba de error grosero.`, '');
  R.note(`Control: ‖A′Pv‖ = ${ex(Math.hypot(...MV(T(PA), v)))}`, '');
  const cl = ob.map((o, i) => [i, o]).filter(([i]) => !used[i]).map(([i, o]) => { const Lc = o.L + LD[o.d] + LD[o.h], tl = 2.5 * sk * Math.sqrt(Lc); return { n: `${i + 1}: ${o.d}-${o.h}`, Lc, w: l[i], tl, ok: Math.abs(l[i]) <= tl }; });
  if (cl.length) R.sec('Cierre de circuitos (lazos fundamentales)', ['Tramo de cierre', 'L lazo [km]', 'Cierre [mm]', 'Tolerancia [mm]', 'Estado'], cl.map(c => [c.n, fx(c.Lc, 2), fx(c.w, 2), fx(c.tl, 2), c.ok ? 'ok' : '<b style="color:#b42318">EXCEDE</b>'])).note('Tolerancia aproximada 2.5·σ_km·√L; L del lazo es una cota superior si los caminos comparten tramos.', '');
  R.csv = 'punto,tipo,H_ajustada_m,sigma_mm\n' + [...(libre ? [] : fj).map(([a, h]) => `${a},FIJO,${h},0`), ...inc.map((a, i) => `${a},LIBRE,${H0[a] + x[i] / 1000},${Math.sqrt(s02 * Q[i][i])}`)].join('\n');
  if (bd.some(Boolean)) { const kb = wv.reduce((m, e, i) => Math.abs(e) > Math.abs(wv[m]) ? i : m, 0); R.note(`<button class="sec" data-a="n_obs" data-k="${kb}" data-r="n">Excluir tramo ${kb + 1} (${ob[kb].d}-${ob[kb].h}) y reajustar</button>`, ''); }
  else if (!ok) R.note(`No hay errores groseros individuales (ningún |w| supera ${fx(wl, 4)}); el χ² ${Tc > hi ? 'alto indica que la σ a priori es optimista' : 'bajo indica que la σ a priori es pesimista'} (σ̂₀ = ${fx(Math.sqrt(s02), 2)}). Revise σ por km.`, '');
  R.top([[ok, 'Test χ² bilateral'], [Tc <= cu, 'Test χ² unilateral'], [f >= 3, `Redundancia f = ${f}` + (f >= 3 ? '' : ' (baja: poca capacidad de detectar errores)')], [!bd.some(Boolean), 'Baarda: sin errores groseros'], [cl.every(c => c.ok), cl.length ? 'Cierres de circuitos dentro de tolerancia' : 'Sin circuitos cerrados que verificar']]);
  return R;
}

/* ===== MÓDULO 2: RED 2D ===== */
const G2R = g => g * Math.PI / 200, R2G = r => r * 200 / Math.PI;
const red = a => ((a + Math.PI) % (2 * Math.PI) + 2 * Math.PI) % (2 * Math.PI) - Math.PI;
function build(d, xy) {
  const { nom, nf, u } = d, ix = k => { const i = nom.indexOf(k); if (i < 0) throw Error('Punto no declarado en puntos.txt: ' + k); return i; };
  const A = [], L = [], L0 = [], sg = [];
  const put = (r, pt, cE, cN) => { if (pt >= nf) { const c = 2 * (pt - nf); r[c] += cE; r[c + 1] += cN; } };
  d.dist.forEach(o => {
    const i = ix(o.a), j = ix(o.b), dE = xy[j][0] - xy[i][0], dN = xy[j][1] - xy[i][1], d0 = Math.hypot(dE, dN), r = Array(u).fill(0);
    put(r, i, -dE / d0, -dN / d0); put(r, j, dE / d0, dN / d0);
    A.push(r); L.push(o.v); L0.push(d0); sg.push(o.s);
  });
  (d.gnss || []).forEach(o => {
    const i = ix(o.a), j = ix(o.b);
    [[0, o.dE, o.sE], [1, o.dN, o.sN]].forEach(([c, v, s]) => { const r = Array(u).fill(0); put(r, i, c ? 0 : -1, c ? -1 : 0); put(r, j, c ? 0 : 1, c ? 1 : 0); A.push(r); L.push(v); L0.push(xy[j][c] - xy[i][c]); sg.push(s); });
  });
  d.ang.forEach(o => {
    const v = ix(o.v), b = ix(o.b), f = ix(o.f), r = Array(u).fill(0);
    const eb = xy[b][0] - xy[v][0], nb = xy[b][1] - xy[v][1], b2 = eb * eb + nb * nb;
    const ef = xy[f][0] - xy[v][0], nfw = xy[f][1] - xy[v][1], f2 = ef * ef + nfw * nfw;
    put(r, b, -nb / b2, eb / b2); put(r, f, nfw / f2, -ef / f2); put(r, v, nb / b2 - nfw / f2, -eb / b2 + ef / f2);
    A.push(r); L.push(G2R(o.g)); L0.push((((Math.atan2(ef, nfw) - Math.atan2(eb, nb)) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)); sg.push(G2R(o.s));
  });
  (d.azi || []).forEach(o => {
    const i = ix(o.a), j = ix(o.b), dE = xy[j][0] - xy[i][0], dN = xy[j][1] - xy[i][1], d2 = dE * dE + dN * dN, r = Array(u).fill(0);
    put(r, i, -dN / d2, dE / d2); put(r, j, dN / d2, -dE / d2);
    A.push(r); L.push(G2R(o.g)); L0.push(((Math.atan2(dE, dN) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)); sg.push(G2R(o.s));
  });
  return { A, L, L0, sg };
}
function runRed() {
  const s02p = +$('r_s02').value, al = +$('r_alfa').value, al0 = +$('r_alfa0').value, tol = +$('r_tol').value, esc = +$('r_esc').value;
  const pts = parse($('r_pts').value, 4, 'puntos.txt').map(r => ({ n: r[0], e: num(r[1], r[0]), no: num(r[2], r[0]), t: r[3].toUpperCase() }));
  pts.forEach(q => { if (!['F', 'N'].includes(q.t)) throw Error(`Punto ${q.n}: tipo "${q.t}" inválido (use F o N).`); });
  const libre = $('r_libre').checked, fij = libre ? [] : pts.filter(q => q.t === 'F'), nue = libre ? pts : pts.filter(q => q.t === 'N');
  const dist = parse($('r_dis').value, 4, 'distancias.txt').map(r => ({ a: r[0], b: r[1], v: num(r[2], r[0]), s: num(r[3], r[0]) }));
  const ang = parse($('r_ang').value, 5, 'angulos.txt').map(r => ({ v: r[0], b: r[1], f: r[2], g: num(r[3], r[0]), s: num(r[4], r[0]) }));
  const azi = parse($('r_azi').value, 4, 'azimuts.txt').map(r => ({ a: r[0], b: r[1], g: num(r[2], r[0]), s: num(r[3], r[0]) }));
  const gnss = parse($('r_gns').value, 6, 'gnss.txt').map(r => ({ a: r[0], b: r[1], dE: num(r[2], r[0]), dN: num(r[3], r[0]), sE: num(r[4], r[0]), sN: num(r[5], r[0]) }));
  if (gnss.some(o => o.sE <= 0 || o.sN <= 0)) throw Error('Revise gnss.txt: las sigmas deben ser > 0.');
  const nom = [...fij, ...nue].map(q => q.n), nf = fij.length, u = 2 * nue.length, n = dist.length + 2 * gnss.length + ang.length + azi.length;
  if (!libre && nf < 2) throw Error(`Ajuste amarrado: se requieren al menos 2 puntos fijos (hay ${nf}).`);
  if (!nue.length) throw Error('No hay puntos nuevos (tipo N).');
  if (new Set(nom).size !== nom.length) throw Error('Hay puntos repetidos.');
  if (!libre && n - u < 1) throw Error(`Redundancia insuficiente: n = ${n}, u = ${u} (se requiere n − u ≥ 1).`);
  if (dist.some(o => o.v <= 0 || o.s <= 0) || ang.some(o => o.s <= 0 || o.g < 0 || o.g >= 400)) throw Error('Revise distancias/ángulos: valores y sigmas deben ser válidos (ángulo 0–400 gon).');
  const ixp = k => { const i = nom.indexOf(k); if (i < 0) throw Error('Punto no declarado en puntos.txt: ' + k); return i; };
  dist.forEach(o => { const i = ixp(o.a), j = ixp(o.b); if (i === j) throw Error('Distancia de un punto a sí mismo: ' + o.a); if (Math.max(i, j) < nf) throw Error(`La distancia ${o.a}-${o.b} une solo puntos fijos: no aporta al ajuste.`); });
  ang.forEach(o => { const t3 = [ixp(o.v), ixp(o.b), ixp(o.f)]; if (new Set(t3).size < 3) throw Error(`Ángulo en ${o.v}: vértice, atrás y adelante deben ser distintos.`); if (Math.max(...t3) < nf) throw Error(`El ángulo en ${o.v} usa solo puntos fijos: no aporta al ajuste.`); });
  if (azi.some(o => o.s <= 0 || o.g < 0 || o.g >= 400)) throw Error('Revise azimuts.txt: sigma > 0 y azimut entre 0 y 400 gon.');
  const nd = dist.length + 2 * gnss.length, d = { nom, nf, u, dist, gnss, ang, azi, off: nd };
  const xy0 = [...fij, ...nue].map(q => [q.e, q.no]);
  const orig = xy0.map(q => q.slice()), its = [];
  const iter = $('r_iter').checked;
  for (let it = 0; iter && it < 10; it++) {
    const b = build(d, xy0), ll = b.L.map((e, i) => i >= nd ? red(e - b.L0[i]) : e - b.L0[i]), pp = b.sg.map(s => s02p / (s * s));
    const PAx = b.A.map((r, i) => r.map(v => v * pp[i])), Nx = MM(T(b.A), PAx), xx = MV(libre ? freeInv(Nx, datumB(b.A, xy0, u)) : inv(Nx), MV(T(PAx), ll));
    its.push(Math.max(...xx.map(Math.abs)));
    if (its[it] < 1e-7) break;
    nue.forEach((_, k) => { xy0[nf + k][0] += xx[2 * k]; xy0[nf + k][1] += xx[2 * k + 1]; });
  }
  const { A, L, L0, sg } = build(d, xy0);
  const l = L.map((e, i) => i >= nd ? red(e - L0[i]) : e - L0[i]);
  const p = sg.map(s => s02p / (s * s)), PA = A.map((r, i) => r.map(v => v * p[i]));
  const N = MM(T(A), PA), nv = MV(T(PA), l), Bm = libre ? datumB(A, xy0, u) : [], Ni = libre ? freeInv(N, Bm) : inv(N), x = MV(Ni, nv);
  const V = A.map((r, i) => dot(r, x) - l[i]);
  if (n - u + Bm.length < 1) throw Error('Redundancia insuficiente incluso en ajuste libre: r = n − u + d < 1.');
  const gl = n - u + Bm.length, vtpv = V.reduce((s, e, i) => s + p[i] * e * e, 0), s02 = vtpv / gl, chi = gl * s02 / s02p;
  const lo = chi2q(al / 2, gl), hi = chi2q(1 - al / 2, gl), cu = chi2q(1 - al, gl), ok = chi >= lo && chi <= hi;
  const AN = MM(A, Ni), hh = AN.map((r, i) => dot(r, A[i]));
  const qv = hh.map((h, i) => 1 / p[i] - h), w = V.map((e, i) => e / Math.sqrt(s02p * qv[i])), ri = qv.map((q, i) => q * p[i]);
  const mdb = i => { const m = 4.13 * Math.sqrt(s02p / (p[i] * ri[i])); return i >= nd ? fx(R2G(m), 5) + ' gon' : fx(m, 4) + ' m'; }, wLim = Math.sqrt(chi2q(1 - al0, 1)), sL = hh.map(h => Math.sqrt(s02 * h));
  const etq = [...dist.map(o => `dist ${o.a}-${o.b}`), ...gnss.flatMap(o => [`GNSS ΔE ${o.a}→${o.b}`, `GNSS ΔN ${o.a}→${o.b}`]), ...ang.map(o => `ang ${o.v} (${o.b}-${o.f})`), ...azi.map(o => `az ${o.a}→${o.b}`)];
  const k95 = Math.sqrt(chi2q(0.95, 2)), sx = Ni.map((r, i) => Math.sqrt(s02 * r[i]));
  const el = nue.map((_, k) => {
    const a = s02 * Ni[2 * k][2 * k], b = s02 * Ni[2 * k][2 * k + 1], c = s02 * Ni[2 * k + 1][2 * k + 1];
    const m = (a + c) / 2, r = Math.hypot((a - c) / 2, b), th = 0.5 * Math.atan2(2 * b, a - c);
    return { a: Math.sqrt(m + r), b: Math.sqrt(Math.max(m - r, 0)), th, az: (((Math.atan2(Math.cos(th), Math.sin(th))) % Math.PI) + Math.PI) % Math.PI * 200 / Math.PI };
  });
  const xyA = [...xy0.slice(0, nf), ...nue.map((q, k) => [xy0[nf + k][0] + x[2 * k], xy0[nf + k][1] + x[2 * k + 1]])];
  const maxX = Math.max(...x.map(Math.abs)), conv = iter ? its[its.length - 1] < 1e-7 : maxX <= tol, bad = w.map(e => Math.abs(e) > wLim), km = w.reduce((m, e, i) => Math.abs(e) > Math.abs(w[m]) ? i : m, 0);
  const R = new Rep().cards([['Observaciones n', n], ['Incógnitas u', u], ['Redundancia r', gl], ['σ₀² a posteriori', fx(s02, 4)], ['χ² calculado', fx(chi, 3)]]);
  R.sec('Coordenadas ajustadas', ['Punto', 'E ajust. [m]', 'N ajust. [m]', 'σE [m]', 'σN [m]', 'dE [m]', 'dN [m]'],
    nue.map((q, k) => [q.n, fx(xyA[nf + k][0], 4), fx(xyA[nf + k][1], 4), fx(sx[2 * k], 4), fx(sx[2 * k + 1], 4), fx(xyA[nf + k][0] - orig[nf + k][0], 4), fx(xyA[nf + k][1] - orig[nf + k][1], 4)]));
  if (!iter) R.note(`máx|x| = ${fx(maxX, 4)} m → ` + verdict(maxX <= tol, 'aproximados suficientes', `AVISO: supera ${tol} m; los aproximados X0 son insuficientes. Repita con las coordenadas ajustadas como X0 o active «Iterar»`), '');
  else R.note(`Iteraciones: ${its.length} · máx|x| por iteración [m]: ${its.map(ex).join(' → ')} → ` + verdict(conv, 'convergió', 'NO convergió: revise datos y coordenadas aproximadas') + (its[0] > tol ? ` (las aproximadas iniciales diferían ${fx(its[0], 3)} m)` : ''), '');
  R.sec('Observaciones ajustadas', ['Observación', 'Observada', 'Ajustada', 'v', 'σ a priori', 'σ ajust.'],
    etq.map((e, i) => i < nd ? [e, fx(L[i], 4), fx(L[i] + V[i], 4), ex(V[i]), ex(sg[i]), ex(sL[i])] : [e + ' [gon]', fx(R2G(L[i]), 5), fx(R2G(L[i] + V[i]), 5), fx(R2G(V[i]), 5), fx(R2G(sg[i]), 5), fx(R2G(sL[i]), 5)]));
  R.sec(`Test de Baarda (límite z = ${fx(wLim, 4)}, α₀ = ${al0})`, ['Observación', 'peso p', 'r_i', 'w', 'MDB (β=20%)', 'Resultado'],
    etq.map((e, i) => [e, ex(p[i]), fx(ri[i], 4), fx(w[i], 4), mdb(i), bad[i] ? '<b style="color:#b42318">ERROR GROSERO</b>' : 'ok']));
  R.note(`Σ r_i = ${fx(ri.reduce((a, b) => a + b, 0), 4)} (debe ser ${gl}). Observación más sospechosa: ${etq[km]} (|w| = ${fx(Math.abs(w[km]), 4)}). ` + (bad.some(Boolean) ? verdict(false, '', 'Supera el límite: verifique/elimine una a la vez y repita.') : verdict(true, 'No se detectan errores groseros.', '')), '');
  R.sec('Elipses de error', ['Punto', 'a 1σ [m]', 'b 1σ [m]', 'Azimut eje mayor [gon]', 'a 95% [m]', 'b 95% [m]'],
    nue.map((q, k) => [q.n, fx(el[k].a, 6), fx(el[k].b, 6), fx(el[k].az, 3), fx(el[k].a * k95, 6), fx(el[k].b * k95, 6)]));
  R.note(`<b>Test χ² bilateral (α=${al}, ${gl} g.l.):</b> χ² = ${fx(chi, 4)} · [${fx(lo, 4)} ; ${fx(hi, 4)}] → ` + verdict(ok, 'SE ACEPTA H₀', chi < lo ? 'SE RECHAZA (χ² bajo: precisiones pesimistas)' : 'SE RECHAZA (χ² alto: errores groseros, pesos o modelo)'), '');
  R.note(`Prueba unilateral: crítico ${fx(cu, 4)} → ` + verdict(chi <= cu, 'SE ACEPTA el modelo', 'SE RECHAZA'), '');
  R.note(`Control: máx|A′PV| = ${ex(Math.max(...MV(T(PA), V).map(Math.abs)))}`, '');
  R.csv = 'punto,tipo,E,N,sigmaE,sigmaN\n' + [...fij.map(q => `${q.n},FIJO,${q.e},${q.no},0,0`), ...nue.map((q, k) => `${q.n},NUEVO,${xyA[nf + k][0]},${xyA[nf + k][1]},${sx[2 * k]},${sx[2 * k + 1]}`)].join('\n');
  const rel = [];
  for (let i = 0; i < nue.length; i++) for (let j = i + 1; j < nue.length; j++) {
    const g = (a, b) => s02 * (Ni[2 * i + a][2 * i + b] + Ni[2 * j + a][2 * j + b] - Ni[2 * i + a][2 * j + b] - Ni[2 * j + a][2 * i + b]);
    const a = g(0, 0), b = g(0, 1), c = g(1, 1), m = (a + c) / 2, r = Math.hypot((a - c) / 2, b), th = 0.5 * Math.atan2(2 * b, a - c);
    rel.push([`${nue[i].n} – ${nue[j].n}`, fx(Math.sqrt(m + r), 6), fx(Math.sqrt(Math.max(m - r, 0)), 6), fx((Math.atan2(Math.cos(th), Math.sin(th)) % Math.PI + Math.PI) % Math.PI * 200 / Math.PI, 3), fx(Math.sqrt(m + r) * k95, 6), fx(Math.sqrt(Math.max(m - r, 0)) * k95, 6)]);
  }
  if (rel.length) R.sec('Elipses de error relativas (entre puntos nuevos)', ['Par', 'a 1σ [m]', 'b 1σ [m]', 'Azimut eje mayor [gon]', 'a 95% [m]', 'b 95% [m]'], rel);
  const prs = [];
  for (let i = 0; i < nom.length; i++) for (let j = i + 1; j < nom.length; j++) {
    if (i < nf && j < nf) continue;
    const C = (p_, a, q_, b) => p_ >= nf && q_ >= nf ? s02 * Ni[2 * (p_ - nf) + a][2 * (q_ - nf) + b] : 0;
    const g = (a, b) => C(i, a, i, b) + C(j, a, j, b) - C(i, a, j, b) - C(j, a, i, b);
    const dE = xyA[j][0] - xyA[i][0], dN = xyA[j][1] - xyA[i][1], D = Math.hypot(dE, dN), uE = dE / D, uN = dN / D;
    const sd = Math.sqrt(uE * uE * g(0, 0) + 2 * uE * uN * g(0, 1) + uN * uN * g(1, 1)), sa = Math.sqrt(uN * uN * g(0, 0) - 2 * uE * uN * g(0, 1) + uE * uE * g(1, 1)) / D;
    prs.push([`${nom[i]} – ${nom[j]}`, fx(D, 4), fx(sd, 5), '1:' + Math.round(D / sd), fx(R2G(((Math.atan2(dE, dN) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)), 4), fx(R2G(sa), 5)]);
  }
  if (prs.length) R.sec('Precisión relativa entre puntos (distancia y azimut ajustados)', ['Par', 'Distancia [m]', 'σ dist [m]', 'Precisión', 'Azimut [gon]', 'σ azimut [gon]'], prs);
  if (bad.some(Boolean)) R.note(`<button class="sec" data-a="${km < dist.length ? 'r_dis' : km < nd ? 'r_gns' : km < nd + ang.length ? 'r_ang' : 'r_azi'}" data-k="${km < dist.length ? km : km < nd ? Math.floor((km - dist.length) / 2) : km < nd + ang.length ? km - nd : km - nd - ang.length}" data-r="r">Excluir «${etq[km]}» y reajustar</button>`, '');
  if (!bad.some(Boolean) && !ok) R.note(`No hay errores groseros individuales (ningún |w| supera ${fx(wLim, 4)}); el χ² ${chi > hi ? 'alto indica que la σ a priori es optimista' : 'bajo indica que la σ a priori es pesimista'} (σ̂₀ = ${fx(Math.sqrt(s02), 2)}). Revise las σ de las observaciones.`, '');
  if (libre) R.note(`<b>Ajuste libre (restricciones interiores):</b> todos los puntos se ajustan; defecto de datum d = ${Bm.length}; r = n − u + d = ${gl}. Qxx = (N + B′B)⁻¹ − B′B (pseudoinversa). Las σ son internas a la red y no dependen de un punto fijo.`, '');
  R.top([[ok, 'Test χ² global bilateral'], [chi <= cu, 'Test χ² unilateral'], [!bad.some(Boolean), 'Baarda: sin errores groseros'], [conv, iter ? 'Iteración convergió' : 'Aproximados suficientes (máx|x| ≤ tolerancia)'], [gl >= 3, `Redundancia r = ${gl}` + (gl >= 3 ? '' : ' (baja)')]]);
  R.extra = plot(d, xyA, nue, el, k95, esc, w, wLim);
  return R;
}
function plot(d, xy, nue, el, k95, esc, w, wLim) {
  const nf = d.nf, W = 760, H = 460, m = 50;
  const xs = xy.map(q => q[0]), ys = xy.map(q => q[1]), x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys);
  const sc = Math.min((W - 2 * m) / Math.max(x1 - x0, 1e-6), (H - 2 * m) / Math.max(y1 - y0, 1e-6));
  const X = e => m + (e - x0) * sc, Y = n => H - m - (n - y0) * sc, ix = k => d.nom.indexOf(k), col = v => `hsl(${120 - 120 * Math.min(Math.abs(v) / wLim, 1)},65%,42%)`;
  let s = `<h3>Red ajustada (elipses 95 % ampliadas ×${esc})</h3><svg viewBox="0 0 ${W} ${H}">`;
  d.dist.forEach((o, q0) => { const i = ix(o.a), j = ix(o.b); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="${col(w[q0])}" stroke-width="2.2"><title>dist ${o.a}-${o.b}: w = ${fx(w[q0], 2)}</title></line>`; });
  (d.gnss || []).forEach(o => { const i = ix(o.a), j = ix(o.b); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="#9333ea" stroke-width="2"><title>GNSS ${o.a}→${o.b}</title></line>`; });
  (d.azi || []).forEach((o, q0) => { const i = ix(o.a), j = ix(o.b); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="${col(w[d.off + d.ang.length + q0])}" stroke-width="2" stroke-dasharray="2 3"><title>az ${o.a}→${o.b}: w = ${fx(w[d.off + d.ang.length + q0], 2)}</title></line>`; });
  d.ang.forEach((o, q0) => [o.b, o.f].forEach(q => { const i = ix(o.v), j = ix(q); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="${col(w[d.off + q0])}" stroke-width="2" stroke-dasharray="5 4"><title>ang ${o.v}: w = ${fx(w[d.off + q0], 2)}</title></line>`; }));
  nue.forEach((q, k) => {
    const e = el[k], c = xy[nf + k], pts = [];
    for (let i = 0; i <= 90; i++) { const t = i / 90 * 2 * Math.PI, ue = e.a * k95 * esc * Math.cos(t), un = e.b * k95 * esc * Math.sin(t); pts.push(`${X(c[0] + ue * Math.cos(e.th) - un * Math.sin(e.th))},${Y(c[1] + ue * Math.sin(e.th) + un * Math.cos(e.th))}`); }
    s += `<polygon points="${pts.join(' ')}" fill="rgba(220,38,38,.1)" stroke="#dc2626"/>`;
  });
  d.nom.forEach((n, i) => {
    const fixed = i < nf, cx = X(xy[i][0]), cy = Y(xy[i][1]);
    s += fixed ? `<rect x="${cx - 6}" y="${cy - 6}" width="12" height="12" fill="#111"/>` : `<circle cx="${cx}" cy="${cy}" r="6" fill="#3b82f6" stroke="#1e40af"/>`;
    s += `<text x="${cx + 10}" y="${cy - 8}" font-size="13" font-weight="600">${n}${fixed ? ' (fijo)' : ''}</text>`;
  });
  return s + '</svg><p class="hint">Color de las líneas: verde = |w| bajo, rojo = cerca o sobre el límite de Baarda (pase el cursor para ver w) · Rueda: zoom · arrastrar: mover · doble clic: restablecer · <a href="#" id="svgd">Descargar figura (SVG)</a></p>';
}

/* ===== Interfaz ===== */
const EX = {
  n_obs: '# desde hasta desnivel_m longitud_km\nA B  1.2343 1.2\nB C  0.5668 0.8\nC D -0.7885 1.0\nD A -1.0122 1.5\nA C  1.8004 2.0\nB D -0.2212 1.1',
  n_fix: '# nombre altura_m\nA 100.000',
  r_pts: '# nombre este norte tipo\nA 1000 2000 F\nB 1200 2000 F\nC 1049.8 2150.2 N\nD 1150.3 2149.8 N',
  r_dis: '# desde hasta dist_m sigma_m\nA C 158.116 0.005\nB C 212.130 0.005\nA D 212.134 0.005\nB D 158.112 0.005\nC D 100.002 0.005',
  r_ang: '# vertice atras adelante gon sigma_gon\nC A D 279.5170 0.0020\nD C B 279.5165 0.0020'
};
EX.r_azi = '# desde hasta azimut_gon sigma_gon\n# ejemplo: A C 379.5167 0.0020';
EX.r_gns = '# desde hasta dE_m dN_m sigmaE_m sigmaN_m\n# ejemplo: A C 49.80 150.20 0.010 0.010';
const loadEx = ks => ks.forEach(k => $(k).value = EX[k]);
document.querySelectorAll('.tab').forEach(t => t.onclick = () => {
  document.querySelectorAll('.tab,.panel').forEach(e => e.classList.remove('on'));
  t.classList.add('on'); $(t.dataset.p).classList.add('on');
});
document.querySelectorAll('input[type=file]').forEach(i => i.onchange = () => {
  const f = i.files[0]; if (!f) return;
  const rd = new FileReader(); rd.onload = () => $(i.dataset.t).value = rd.result; rd.readAsText(f);
});
const dl = id => () => {
  if (!texts[id]) return alert('Primero ejecute el ajuste.');
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([texts[id]], { type: 'text/plain' }));
  a.download = id === 'rn' ? 'reporte_nivelacion.txt' : 'reporte_ajuste_2D.txt'; a.click();
};
$('bn').onclick = () => show('rn', runNiv); $('br').onclick = () => show('rr', runRed);
$('en').onclick = () => { loadEx(['n_obs', 'n_fix']); show('rn', runNiv); };
$('er').onclick = () => { loadEx(['r_pts', 'r_dis', 'r_ang', 'r_azi', 'r_gns']); show('rr', runRed); };
$('dn').onclick = dl('rn'); $('dr').onclick = dl('rr');
const dc = id => () => { if (!csvs[id]) return alert('Primero ejecute el ajuste.'); const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob(['\uFEFF' + csvs[id]], { type: 'text/csv' })); a.download = id === 'rn' ? 'alturas_ajustadas.csv' : 'coordenadas_ajustadas.csv'; a.click(); };
$('cn').onclick = dc('rn'); $('cr').onclick = dc('rr'); $('pn_').onclick = $('pr_').onclick = () => window.print();
loadEx(Object.keys(EX));

/* ===== Depuración, proyectos y arrastrar-soltar ===== */
document.addEventListener('click', e => {
  const b = e.target.closest('[data-a]'); if (!b) return;
  const ln = $(b.dataset.a).value.split('\n'); let c = -1;
  for (let i = 0; i < ln.length; i++) if (ln[i].split('#')[0].trim() && ++c === +b.dataset.k) { ln[i] = '# [excluida] ' + ln[i]; break; }
  $(b.dataset.a).value = ln.join('\n');
  b.dataset.r === 'r' ? show('rr', runRed) : show('rn', runNiv);
});
const PID = ['n_obs', 'n_fix', 'n_s0', 'n_alfa', 'n_alfa0', 'n_sk', 'r_pts', 'r_dis', 'r_ang', 'r_azi', 'r_gns', 'r_s02', 'r_alfa', 'r_alfa0', 'r_tol', 'r_esc', 'p_nom', 'p_op', 'p_dec'];
$('gp').onclick = () => {
  const o = {}; PID.forEach(k => o[k] = $(k).value);
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([JSON.stringify(o, null, 1)], { type: 'application/json' }));
  a.download = ($('p_nom').value.trim() || 'proyecto_ajuste') + '.json'; a.click();
};
$('cp').onchange = ev => {
  const f = ev.target.files[0]; if (!f) return;
  const rd = new FileReader();
  rd.onload = () => { try { const o = JSON.parse(rd.result); PID.forEach(k => { if (k in o) $(k).value = o[k]; }); } catch (_) { alert('Archivo de proyecto inválido.'); } };
  rd.readAsText(f); ev.target.value = '';
};
document.querySelectorAll('textarea').forEach(t => {
  t.ondragover = e => e.preventDefault();
  t.ondrop = e => { e.preventDefault(); const f = e.dataTransfer.files[0]; if (!f) return; const rd = new FileReader(); rd.onload = () => t.value = rd.result; rd.readAsText(f); };
});

/* ===== Zoom / desplazamiento / exportación de la figura ===== */
function enableZoom() {
  const s = document.querySelector('#rr svg'); if (!s) return;
  const v0 = s.getAttribute('viewBox').split(' ').map(Number); let v = v0.slice(), drag = null;
  const set = () => s.setAttribute('viewBox', v.join(' '));
  s.addEventListener('wheel', e => {
    e.preventDefault(); const r = s.getBoundingClientRect(), fxr = (e.clientX - r.left) / r.width, fyr = (e.clientY - r.top) / r.height, k = e.deltaY < 0 ? 0.85 : 1.18;
    const px = v[0] + fxr * v[2], py = v[1] + fyr * v[3]; v[2] *= k; v[3] *= k; v[0] = px - fxr * v[2]; v[1] = py - fyr * v[3]; set();
  }, { passive: false });
  s.onmousedown = e => { drag = [e.clientX, e.clientY, v[0], v[1]]; s.style.cursor = 'grabbing'; };
  window.addEventListener('mouseup', () => { drag = null; s.style.cursor = ''; });
  s.onmousemove = e => { if (!drag) return; const r = s.getBoundingClientRect(); v[0] = drag[2] - (e.clientX - drag[0]) * v[2] / r.width; v[1] = drag[3] - (e.clientY - drag[1]) * v[3] / r.height; set(); };
  s.ondblclick = () => { v = v0.slice(); set(); };
  $('svgd').onclick = e => {
    e.preventDefault(); const c = s.cloneNode(true); c.setAttribute('xmlns', 'http://www.w3.org/2000/svg'); c.setAttribute('viewBox', v0.join(' '));
    c.insertAdjacentHTML('afterbegin', `<rect width="100%" height="100%" fill="#fff"/>`);
    const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([c.outerHTML], { type: 'image/svg+xml' })); a.download = 'red_ajustada.svg'; a.click();
  };
}
