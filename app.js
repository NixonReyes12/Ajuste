'use strict';
/* ===== Utilidades ===== */
const $ = i => document.getElementById(i), fx = (v, d = 4) => Number(v).toFixed(d), ex = v => Number(v).toExponential(3);
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
function parse(txt, nc, name) {
  const rows = [];
  txt.split(/\r?\n/).forEach((ln, i) => {
    ln = ln.replace(/^\uFEFF/, '').split('#')[0].trim(); if (!ln) return;
    const c = ln.split(/[\s,;]+/);
    if (c.length !== nc) throw Error(`${name}, línea ${i + 1}: se esperan ${nc} columnas.`);
    rows.push(c);
  });
  return rows;
}
const num = (s, name) => { const v = Number(s); if (!isFinite(v) || s === '') throw Error(`${name}: "${s}" no es un número válido.`); return v; };
/* Constructor de reporte (HTML + TXT) */
class Rep {
  constructor() { this.h = ''; this.t = 'REPORTE DE AJUSTE POR MINIMOS CUADRADOS (METODO PARAMETRICO)\n' + new Date().toLocaleString() + '\n'; }
  cards(a) { this.h += '<div class="cards">' + a.map(([k, v]) => `<div class="k"><b>${v}</b><span>${k}</span></div>`).join('') + '</div>'; return this; }
  sec(title, hd, rows) {
    this.h += `<h3>${title}</h3><div class="tw"><table><thead><tr>${hd.map(x => `<th>${x}</th>`).join('')}</tr></thead><tbody>${rows.map(r => `<tr>${r.map(x => `<td>${x}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
    this.t += `\n${title}\n${'-'.repeat(90)}\n` + [hd, ...rows].map(r => r.map((x, i) => String(x).replace(/<[^>]+>/g, '')[i ? 'padStart' : 'padEnd'](i ? 16 : 22)).join('')).join('\n') + '\n';
    return this;
  }
  note(s, cls) { this.h += `<p class="${cls || ''}">${s}</p>`; this.t += s.replace(/<[^>]+>/g, '') + '\n'; return this; }
}
const texts = {};
function show(id, fn) {
  try { const r = fn(); texts[id] = r.t; $(id).innerHTML = `<div class="card">${r.h}${r.extra || ''}</div>`; }
  catch (e) { $(id).innerHTML = `<div class="err">⚠ ${e.message}</div>`; }
}
const verdict = (ok, a, b) => `<span class="${ok ? 'ok' : 'bad'}">${ok ? a : b}</span>`;

/* ===== MÓDULO 1: NIVELACIÓN ===== */
function runNiv() {
  const s0 = +$('n_s0').value, al = +$('n_alfa').value, sk = +$('n_sk').value;
  const ob = parse($('n_obs').value, 4, 'nivelacion.txt').map(r => ({ d: r[0], h: r[1], dh: num(r[2], r[0] + '-' + r[1]), L: num(r[3], r[0] + '-' + r[1]) }));
  const fj = parse($('n_fix').value, 2, 'fijos_nivelacion.txt').map(r => [r[0], num(r[1], r[0])]);
  if (!ob.length) throw Error('No hay observaciones.');
  if (!fj.length) throw Error('Indique al menos un punto fijo.');
  if (ob.some(o => o.L <= 0)) throw Error('Las longitudes deben ser positivas.');
  if (ob.some(o => o.d === o.h)) throw Error('Hay un tramo con el mismo punto de salida y llegada.');
  const all = [...new Set(ob.flatMap(o => [o.d, o.h]))];
  fj.forEach(([n]) => { if (!all.includes(n)) throw Error('Punto fijo inexistente en la red: ' + n); });
  const H0 = {}; fj.forEach(([n, h]) => H0[n] = h);
  const used = ob.map(() => false);
  for (let ch = true; ch;) {
    ch = false;
    ob.forEach((o, i) => {
      if (used[i]) return;
      if (o.d in H0 && !(o.h in H0)) { H0[o.h] = H0[o.d] + o.dh; used[i] = ch = true; }
      else if (o.h in H0 && !(o.d in H0)) { H0[o.d] = H0[o.h] - o.dh; used[i] = ch = true; }
    });
  }
  const lost = all.filter(p => !(p in H0));
  if (lost.length) throw Error('Puntos no conectados con ningún punto fijo: ' + lost.join(', '));
  const inc = all.filter(p => !fj.some(f => f[0] === p)), u = inc.length, n = ob.length, f = n - u;
  if (!u) throw Error('La red no tiene puntos desconocidos.');
  if (f <= 0) throw Error(`Redundancia f = ${f}: no hay control estadístico.`);
  const A = ob.map(o => inc.map(p => (p === o.h) - (p === o.d)));
  const l = ob.map(o => (o.dh - (H0[o.h] - H0[o.d])) * 1000);
  const sg = ob.map(o => sk * Math.sqrt(o.L)), p = sg.map(s => s0 * s0 / (s * s));
  const PA = A.map((r, i) => r.map(v => v * p[i])), N = MM(T(A), PA), t = MV(T(PA), l);
  const Q = inv(N), x = MV(Q, t), v = A.map((r, i) => dot(r, x) - l[i]);
  const vPv = v.reduce((s, e, i) => s + p[i] * e * e, 0), s02 = vPv / f, Tc = vPv / (s0 * s0);
  const lo = chi2q(al / 2, f), hi = chi2q(1 - al / 2, f), cu = chi2q(1 - al, f), ok = Tc >= lo && Tc <= hi;
  const AQ = MM(A, Q), sL = AQ.map((r, i) => Math.sqrt(s02 * dot(r, A[i])));
  const im = v.reduce((m, e, i) => Math.abs(e) > Math.abs(v[m]) ? i : m, 0);
  const R = new Rep().cards([['Observaciones n', n], ['Incógnitas u', u], ['Redundancia f', f], ['σ₀ a posteriori', fx(Math.sqrt(s02), 4)], ['T = v′Pv/σ₀²', fx(Tc, 3)]]);
  R.sec('Alturas ajustadas', ['Punto', 'Tipo', 'H aprox [m]', 'Corrección [mm]', 'H ajustada [m]', 'σ [mm]'],
    [...fj.map(([n_, h]) => [n_, 'FIJO', fx(h), '0.000', fx(h), '0.000']), ...inc.map((n_, i) => [n_, 'LIBRE', fx(H0[n_]), fx(x[i], 3), fx(H0[n_] + x[i] / 1000), fx(Math.sqrt(s02 * Q[i][i]), 3)])]);
  R.sec('Observaciones y residuos', ['Tramo', 'L [km]', 'σ [mm]', 'peso', 'dh obs [m]', 'v [mm]', 'dh ajust [m]', 'σ ajust [mm]'],
    ob.map((o, i) => [`${i + 1}: ${o.d}-${o.h}`, fx(o.L, 3), fx(sg[i], 3), fx(p[i], 5), fx(o.dh), fx(v[i], 3), fx(o.dh + v[i] / 1000), fx(sL[i], 3)]));
  R.sec('Matriz N = A′PA [mm⁻²]', ['', ...inc], N.map((r, i) => [inc[i], ...r.map(e => fx(e, 5))]));
  R.sec('Cofactor Qxx = N⁻¹ [mm²]', ['', ...inc], Q.map((r, i) => [inc[i], ...r.map(e => fx(e, 5))]));
  R.note(`<b>Test χ² bilateral (α=${al}, ${f} g.l.):</b> T = ${fx(Tc, 4)} · intervalo [${fx(lo, 4)} ; ${fx(hi, 4)}] → ` + verdict(ok, 'PASA', Tc < lo ? 'NO PASA (T bajo: precisiones a priori pesimistas)' : 'NO PASA (T alto: errores en datos o σ optimista)'), '');
  R.note(`<b>Prueba unilateral:</b> crítico ${fx(cu, 4)} → ` + verdict(Tc <= cu, 'SE ACEPTA el modelo', 'SE RECHAZA: revisar observaciones'), '');
  R.note(`Mayor residuo: tramo ${im + 1} (${ob[im].d}-${ob[im].h}), |v| = ${fx(Math.abs(v[im]), 3)} mm. Es un indicio a investigar, no una prueba de error grosero.`, '');
  R.note(`Control: ‖A′Pv‖ = ${ex(Math.hypot(...MV(T(PA), v)))}`, '');
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
  d.ang.forEach(o => {
    const v = ix(o.v), b = ix(o.b), f = ix(o.f), r = Array(u).fill(0);
    const eb = xy[b][0] - xy[v][0], nb = xy[b][1] - xy[v][1], b2 = eb * eb + nb * nb;
    const ef = xy[f][0] - xy[v][0], nfw = xy[f][1] - xy[v][1], f2 = ef * ef + nfw * nfw;
    put(r, b, -nb / b2, eb / b2); put(r, f, nfw / f2, -ef / f2); put(r, v, nb / b2 - nfw / f2, -eb / b2 + ef / f2);
    A.push(r); L.push(G2R(o.g)); L0.push((((Math.atan2(ef, nfw) - Math.atan2(eb, nb)) % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)); sg.push(G2R(o.s));
  });
  return { A, L, L0, sg };
}
function runRed() {
  const s02p = +$('r_s02').value, al = +$('r_alfa').value, al0 = +$('r_alfa0').value, tol = +$('r_tol').value, esc = +$('r_esc').value;
  const pts = parse($('r_pts').value, 4, 'puntos.txt').map(r => ({ n: r[0], e: num(r[1], r[0]), no: num(r[2], r[0]), t: r[3].toUpperCase() }));
  pts.forEach(q => { if (!['F', 'N'].includes(q.t)) throw Error(`Punto ${q.n}: tipo "${q.t}" inválido (use F o N).`); });
  const fij = pts.filter(q => q.t === 'F'), nue = pts.filter(q => q.t === 'N');
  const dist = parse($('r_dis').value, 4, 'distancias.txt').map(r => ({ a: r[0], b: r[1], v: num(r[2], r[0]), s: num(r[3], r[0]) }));
  const ang = parse($('r_ang').value, 5, 'angulos.txt').map(r => ({ v: r[0], b: r[1], f: r[2], g: num(r[3], r[0]), s: num(r[4], r[0]) }));
  const nom = [...fij, ...nue].map(q => q.n), nf = fij.length, u = 2 * nue.length, n = dist.length + ang.length;
  if (nf < 2) throw Error(`Ajuste amarrado: se requieren al menos 2 puntos fijos (hay ${nf}).`);
  if (!nue.length) throw Error('No hay puntos nuevos (tipo N).');
  if (new Set(nom).size !== nom.length) throw Error('Hay puntos repetidos.');
  if (n - u < 1) throw Error(`Redundancia insuficiente: n = ${n}, u = ${u} (se requiere n − u ≥ 1).`);
  if (dist.some(o => o.v <= 0 || o.s <= 0) || ang.some(o => o.s <= 0 || o.g < 0 || o.g >= 400)) throw Error('Revise distancias/ángulos: valores y sigmas deben ser válidos (ángulo 0–400 gon).');
  const d = { nom, nf, u, dist, ang }, nd = dist.length;
  const xy0 = [...fij, ...nue].map(q => [q.e, q.no]);
  const { A, L, L0, sg } = build(d, xy0);
  const l = L.map((e, i) => i >= nd ? red(e - L0[i]) : e - L0[i]);
  const p = sg.map(s => s02p / (s * s)), PA = A.map((r, i) => r.map(v => v * p[i]));
  const N = MM(T(A), PA), nv = MV(T(PA), l), Ni = inv(N), x = MV(Ni, nv);
  const V = A.map((r, i) => dot(r, x) - l[i]);
  const gl = n - u, vtpv = V.reduce((s, e, i) => s + p[i] * e * e, 0), s02 = vtpv / gl, chi = gl * s02 / s02p;
  const lo = chi2q(al / 2, gl), hi = chi2q(1 - al / 2, gl), cu = chi2q(1 - al, gl), ok = chi >= lo && chi <= hi;
  const AN = MM(A, Ni), hh = AN.map((r, i) => dot(r, A[i]));
  const qv = hh.map((h, i) => 1 / p[i] - h), w = V.map((e, i) => e / Math.sqrt(s02p * qv[i])), ri = qv.map((q, i) => q * p[i]);
  const wLim = Math.sqrt(chi2q(1 - al0, 1)), sL = hh.map(h => Math.sqrt(s02 * h));
  const etq = [...dist.map(o => `dist ${o.a}-${o.b}`), ...ang.map(o => `ang ${o.v} (${o.b}-${o.f})`)];
  const k95 = Math.sqrt(chi2q(0.95, 2)), sx = Ni.map((r, i) => Math.sqrt(s02 * r[i]));
  const el = nue.map((_, k) => {
    const a = s02 * Ni[2 * k][2 * k], b = s02 * Ni[2 * k][2 * k + 1], c = s02 * Ni[2 * k + 1][2 * k + 1];
    const m = (a + c) / 2, r = Math.hypot((a - c) / 2, b), th = 0.5 * Math.atan2(2 * b, a - c);
    return { a: Math.sqrt(m + r), b: Math.sqrt(Math.max(m - r, 0)), th, az: (((Math.atan2(Math.cos(th), Math.sin(th))) % Math.PI) + Math.PI) % Math.PI * 200 / Math.PI };
  });
  const xyA = [...xy0.slice(0, nf), ...nue.map((q, k) => [q.e + x[2 * k], q.no + x[2 * k + 1]])];
  const maxX = Math.max(...x.map(Math.abs)), bad = w.map(e => Math.abs(e) > wLim), km = w.reduce((m, e, i) => Math.abs(e) > Math.abs(w[m]) ? i : m, 0);
  const R = new Rep().cards([['Observaciones n', n], ['Incógnitas u', u], ['Redundancia r', gl], ['σ₀² a posteriori', fx(s02, 4)], ['χ² calculado', fx(chi, 3)]]);
  R.sec('Coordenadas ajustadas', ['Punto', 'E ajust. [m]', 'N ajust. [m]', 'σE [m]', 'σN [m]', 'dE [m]', 'dN [m]'],
    nue.map((q, k) => [q.n, fx(xyA[nf + k][0], 4), fx(xyA[nf + k][1], 4), fx(sx[2 * k], 4), fx(sx[2 * k + 1], 4), fx(x[2 * k], 4), fx(x[2 * k + 1], 4)]));
  R.note(`máx|x| = ${fx(maxX, 4)} m → ` + verdict(maxX <= tol, 'aproximados suficientes', `supera ${tol} m: repita usando las coordenadas ajustadas como aproximadas`), '');
  R.sec('Observaciones ajustadas', ['Observación', 'Observada', 'Ajustada', 'v', 'σ a priori', 'σ ajust.'],
    etq.map((e, i) => i < nd ? [e, fx(L[i], 4), fx(L[i] + V[i], 4), ex(V[i]), ex(sg[i]), ex(sL[i])] : [e + ' [gon]', fx(R2G(L[i]), 5), fx(R2G(L[i] + V[i]), 5), fx(R2G(V[i]), 5), fx(R2G(sg[i]), 5), fx(R2G(sL[i]), 5)]));
  R.sec(`Test de Baarda (límite z = ${fx(wLim, 4)}, α₀ = ${al0})`, ['Observación', 'peso p', 'r_i', 'w', 'Resultado'],
    etq.map((e, i) => [e, ex(p[i]), fx(ri[i], 4), fx(w[i], 4), bad[i] ? '<b style="color:#b42318">ERROR GROSERO</b>' : 'ok']));
  R.note(`Σ r_i = ${fx(ri.reduce((a, b) => a + b, 0), 4)} (debe ser ${gl}). Observación más sospechosa: ${etq[km]} (|w| = ${fx(Math.abs(w[km]), 4)}). ` + (bad.some(Boolean) ? verdict(false, '', 'Supera el límite: verifique/elimine una a la vez y repita.') : verdict(true, 'No se detectan errores groseros.', '')), '');
  R.sec('Elipses de error', ['Punto', 'a 1σ [m]', 'b 1σ [m]', 'Azimut eje mayor [gon]', 'a 95% [m]', 'b 95% [m]'],
    nue.map((q, k) => [q.n, fx(el[k].a, 6), fx(el[k].b, 6), fx(el[k].az, 3), fx(el[k].a * k95, 6), fx(el[k].b * k95, 6)]));
  R.note(`<b>Test χ² bilateral (α=${al}, ${gl} g.l.):</b> χ² = ${fx(chi, 4)} · [${fx(lo, 4)} ; ${fx(hi, 4)}] → ` + verdict(ok, 'SE ACEPTA H₀', chi < lo ? 'SE RECHAZA (χ² bajo: precisiones pesimistas)' : 'SE RECHAZA (χ² alto: errores groseros, pesos o modelo)'), '');
  R.note(`Prueba unilateral: crítico ${fx(cu, 4)} → ` + verdict(chi <= cu, 'SE ACEPTA el modelo', 'SE RECHAZA'), '');
  R.note(`Control: máx|A′PV| = ${ex(Math.max(...MV(T(PA), V).map(Math.abs)))}`, '');
  R.extra = plot(d, xyA, nue, el, k95, esc);
  return R;
}
function plot(d, xy, nue, el, k95, esc) {
  const nf = d.nf, W = 760, H = 460, m = 50;
  const xs = xy.map(q => q[0]), ys = xy.map(q => q[1]), x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys);
  const sc = Math.min((W - 2 * m) / Math.max(x1 - x0, 1e-6), (H - 2 * m) / Math.max(y1 - y0, 1e-6));
  const X = e => m + (e - x0) * sc, Y = n => H - m - (n - y0) * sc, ix = k => d.nom.indexOf(k);
  let s = `<h3>Red ajustada (elipses 95 % ampliadas ×${esc})</h3><svg viewBox="0 0 ${W} ${H}">`;
  d.dist.forEach(o => { const i = ix(o.a), j = ix(o.b); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="#7a8599" stroke-width="1.4"/>`; });
  d.ang.forEach(o => [o.b, o.f].forEach(q => { const i = ix(o.v), j = ix(q); s += `<line x1="${X(xy[i][0])}" y1="${Y(xy[i][1])}" x2="${X(xy[j][0])}" y2="${Y(xy[j][1])}" stroke="#16a34a" stroke-dasharray="5 4"/>`; }));
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
  return s + '</svg>';
}

/* ===== Interfaz ===== */
const EX = {
  n_obs: '# desde hasta desnivel_m longitud_km\nA B  1.2343 1.2\nB C  0.5668 0.8\nC D -0.7885 1.0\nD A -1.0122 1.5\nA C  1.8004 2.0\nB D -0.2212 1.1',
  n_fix: '# nombre altura_m\nA 100.000',
  r_pts: '# nombre este norte tipo\nA 1000 2000 F\nB 1200 2000 F\nC 1049.8 2150.2 N\nD 1150.3 2149.8 N',
  r_dis: '# desde hasta dist_m sigma_m\nA C 158.116 0.005\nB C 212.130 0.005\nA D 212.134 0.005\nB D 158.112 0.005\nC D 100.002 0.005',
  r_ang: '# vertice atras adelante gon sigma_gon\nC A D 279.5170 0.0020\nD C B 279.5165 0.0020'
};
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
$('er').onclick = () => { loadEx(['r_pts', 'r_dis', 'r_ang']); show('rr', runRed); };
$('dn').onclick = dl('rn'); $('dr').onclick = dl('rr');
loadEx(Object.keys(EX));
