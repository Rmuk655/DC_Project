// KMap-Minimizer Web Simulator (final fixed)
// Single-file React component: function App()

const { useState, useMemo } = React;

// Utilities
const bin = (n, bits) => n.toString(2).padStart(bits, "0");
const popcount = s => s.split("").filter(ch => ch === "1").length;

// Quine-McCluskey implementation (basic, supports don't-cares '-')
function combinePair(a, b) {
    let diff = 0;
    let res = "";
    for (let i = 0; i < a.length; i++) {
        if (a[i] !== b[i]) {
            diff++;
            res += "-";
        } else res += a[i];
    }
    return diff === 1 ? res : null;
}

function removeDuplicates(arr) {
    return [...new Set(arr)];
}

function findPrimeImplicants(minterms) {
    let current = removeDuplicates(minterms.slice());
    let primes = [];
    while (true) {
        const grouped = {};
        current.forEach(m => {
            const key = (m.match(/1/g) || []).length;
            grouped[key] = grouped[key] || [];
            grouped[key].push(m);
        });
        const next = [];
        const marked = new Set();
        const keys = Object.keys(grouped).map(k => parseInt(k)).sort((a, b) => a - b);
        for (let i = 0; i < keys.length - 1; i++) {
            const g1 = grouped[keys[i]];
            const g2 = grouped[keys[i + 1]];
            g1.forEach(a => {
                g2.forEach(b => {
                    const c = combinePair(a, b);
                    if (c) {
                        next.push(c);
                        marked.add(a);
                        marked.add(b);
                    }
                });
            });
        }
        current.forEach(m => {
            if (!marked.has(m)) primes.push(m);
        });
        if (next.length === 0) break;
        current = removeDuplicates(next);
    }
    return removeDuplicates(primes);
}

function covers(implicant, minterm) {
    for (let i = 0; i < implicant.length; i++) {
        if (implicant[i] === "-") continue;
        if (implicant[i] !== minterm[i]) return false;
    }
    return true;
}

function expandMinterm(term) {
    const results = [];
    function rec(prefix, i) {
        if (i === term.length) return results.push(prefix);
        if (term[i] === "-") {
            rec(prefix + "0", i + 1);
            rec(prefix + "1", i + 1);
        } else rec(prefix + term[i], i + 1);
    }
    rec("", 0);
    return results;
}

function implicantToProduct(implicant, varNames) {
    const lits = [];
    for (let i = 0; i < implicant.length; i++) {
        if (implicant[i] === "-") continue;
        lits.push(implicant[i] === "1" ? varNames[i] : `!${varNames[i]}`);
    }
    return lits.length ? lits.join(" & ") : "1";
}

function toLiteral(implicant, varNames) {
    let parts = [];
    for (let i = 0; i < implicant.length; i++) {
        if (implicant[i] === "-") continue;
        parts.push((implicant[i] === "1" ? "" : "~") + varNames[i]);
    }
    return parts.length ? parts.join(" & ") : "1";
}

// convert implicant to POS clause (sum / OR form) for zeros simplification.
function implicantToSumClause(implicant, varNames) {
    const lits = [];
    for (let i = 0; i < implicant.length; i++) {
        if (implicant[i] === "-") continue;
        // for zeros implicant: '0' -> var (A), '1' -> ~var
        lits.push(implicant[i] === "0" ? varNames[i] : `~${varNames[i]}`);
    }
    return lits.length ? `(${lits.join(" + ")})` : "(0)";
}

function solveQM(mintermIndices, dontcaresIndices, n) {
    const all = [...mintermIndices, ...dontcaresIndices].sort((a, b) => a - b);
    const binAll = all.map(x => bin(x, n));
    const primes = findPrimeImplicants(binAll);
    const minBins = mintermIndices.map(x => bin(x, n));
    const chart = {};
    primes.forEach((p, pi) => {
        chart[pi] = [];
        minBins.forEach((m, mi) => {
            if (covers(p, m)) chart[pi].push(mi);
        });
    });
    const coverCount = new Array(minBins.length).fill(0);
    Object.values(chart).forEach(arr => arr.forEach(mi => coverCount[mi]++));
    const essential = new Set();
    coverCount.forEach((c, mi) => {
        if (c === 1) {
            for (const pi in chart) if (chart[pi].includes(mi)) essential.add(parseInt(pi));
        }
    });
    const selected = new Set([...essential]);
    const coveredMins = new Set();
    selected.forEach(pi => chart[pi].forEach(mi => coveredMins.add(mi)));
    while (coveredMins.size < minBins.length) {
        let best = null, bestCount = -1;
        for (const pi in chart) {
            if (selected.has(parseInt(pi))) continue;
            const count = chart[pi].filter(mi => !coveredMins.has(mi)).length;
            if (count > bestCount) { best = parseInt(pi); bestCount = count; }
        }
        if (best === null) break;
        selected.add(best);
        chart[best].forEach(mi => coveredMins.add(mi));
    }
    const implicants = [...selected].map(pi => primes[pi]);
    return implicants;
}

// kmap coordinates
function kmapCoords(index, n) {
    if (n === 1) return [0, index];
    if (n === 2) {
        const row = (index >> 1) & 1;
        const col = index & 1;
        const gray = [0, 1];
        return [gray[row], gray[col]];
    }
    if (n === 3) {
        const row = (index & 4) >> 2;
        const colGray = (index & 3);
        const grayToCol = [0, 1, 3, 2];
        return [row, grayToCol[colGray]];
    }
    if (n === 4) {
        const a = (index >> 3) & 1;
        const b = (index >> 2) & 1;
        const c = (index >> 1) & 1;
        const d = index & 1;
        const rowBinary = (a << 1) | b;
        const colBinary = (c << 1) | d;
        const grayMap = [0, 1, 3, 2];
        return [grayMap[rowBinary], grayMap[colBinary]];
    }
    if (n === 5) {
        const a = (index >> 4) & 1;
        const b = (index >> 3) & 1;
        const c = (index >> 2) & 1;
        const d = (index >> 1) & 1;
        const e = index & 1;
        const rowBinary = (a << 1) | b;
        const colBinary = (c << 2) | (d << 1) | e;
        const gray3 = [0, 1, 3, 2, 6, 7, 5, 4];
        const gray2 = [0, 1, 3, 2];
        return [gray2[rowBinary], gray3[colBinary]];
    }
    return [0, index];
}

// Safe SVG builder
function escapeHtml(s) {
    return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}
function drawLogicSVG(expr, width = 560, height = 120) {
    const escaped = escapeHtml(expr);
    return `<svg xmlns='http://www.w3.org/2000/svg' width='${width}' height='${height}'>
    <rect x='0' y='0' width='100%' height='100%' rx='10' fill='white' stroke='#444'/>
    <foreignObject x='8' y='8' width='${width - 16}' height='${height - 16}'>
      <div xmlns='http://www.w3.org/1999/xhtml' style='font-family:monospace;font-size:12px;color:#111;padding:6px;white-space:pre;'>${escaped}</div>
    </foreignObject>
  </svg>`;
}

function App() {
    const [vars, setVars] = useState(4);
    const varNames = useMemo(() => Array.from({ length: vars }, (_, i) => String.fromCharCode(65 + i)), [vars]);
    const total = 1 << vars;
    const makeInit = (v) => Array.from({ length: 1 << v }, (_, i) => ({ index: i, val: '0' }));
    const [table, setTable] = useState(makeInit(vars));
    const [lastResult, setLastResult] = useState(null);

    // ensure table length matches vars when vars changes (keeps values if possible)
    React.useEffect(() => {
        setTable(prev => {
            const newLen = 1 << vars;
            if (!Array.isArray(prev) || prev.length !== newLen) return makeInit(vars);
            // if length matches, keep prev
            return prev.slice(0, newLen).map((r, i) => r || { index: i, val: '0' });
        });
        setLastResult(null);
    }, [vars]);

    function setCell(i, val) {
        setTable(prev => {
            const copy = prev.slice();
            copy[i] = { index: i, val: String(val) };
            return copy;
        });
    }

    function generateKMAndMinimize() {
        // Defensive: ensure table is array and entries present
        if (!Array.isArray(table)) return alert('Internal error: table missing');
        const mintermIndices = table.filter(r => r && String(r.val) === '1').map(r => r.index);
        const dcIndices = table.filter(r => r && typeof r.val === 'string' && r.val.toLowerCase() === 'x').map(r => r.index);

        const implicants = solveQM(mintermIndices, dcIndices, vars);

        const humanSOP = implicants.map(imp => toLiteral(imp, varNames)).join(' + ') || '0';
        const codeSOP = implicants.map(imp => implicantToProduct(imp, varNames)).join(' || ') || '0';

        function generateVerilog(n, implicants) {
            const moduleName = `kmap_${n}v`;
            const inputs = varNames.join(', ');
            const expr = implicants.length ? implicants.map(imp => {
                const parts = [];
                for (let i = 0; i < imp.length; i++) {
                    if (imp[i] === '-') continue;
                    parts.push(imp[i] === '1' ? varNames[i] : `~${varNames[i]}`);
                }
                return parts.length ? `(${parts.join(' & ')})` : '1';
            }).join(' | ') : '0';
            const verilog = `module ${moduleName}(${inputs}, out);
  input ${varNames.join(', ')};
  output out;
  assign out = ${expr.replace(/~/g, '!')};
endmodule`;
            return verilog;
        }

        const verilogModule = generateVerilog(vars, implicants);

        function generateTestbench(n, table) {
            const moduleName = `kmap_${n}v`;
            const tb = `// Testbench for ${moduleName}
module tb();
  reg ${varNames.join(', ')};
  wire out;
  ${moduleName} dut (${varNames.join(', ')}, out);
  initial begin
    $display("time ${varNames.join(' ')} out");
` + table.map(r => {
                // guard r
                if (!r) return '';
                const bits = bin(r.index, n).split('').map((b, i) => `${varNames[i]}=${b}`).join(', ');
                return `    ${bits}; #1 $display("%0t${varNames.map(() => ' %b').join('')} %b", $time, ${varNames.join(', ')}, out);`;
            }).filter(Boolean).join('\n') + `
    $finish;
  end
endmodule`;
            return tb;
        }

        const testbench = generateTestbench(vars, table);

        const zeroIndices = table.filter(r => r && String(r.val) === '0').map(r => r.index);
        const posImplicants = zeroIndices.length ? solveQM(zeroIndices, dcIndices, vars) : [];
        const humanPOS = posImplicants.map(imp => implicantToSumClause(imp, varNames)).join(' & ') || '1';

        const svgText = `SOP: ${humanSOP}\nPOS: ${humanPOS}`;
        const svg = drawLogicSVG(svgText, 640, Math.max(120, 18 * Math.ceil(svgText.split('\n').length)));

        setLastResult({
            implicants,
            sopCode: codeSOP,
            humanSOP,
            humanPOS,
            verilogModule,
            testbench,
            svg
        });
    }

    function exportFiles() {
        if (!lastResult) return alert('Generate first');
        const zipData = {
            'kmap_run.txt': JSON.stringify({ vars, table }, null, 2),
            'module.v': lastResult.verilogModule,
            'testbench.v': lastResult.testbench,
            'minimized_SOP.txt': lastResult.humanSOP,
            'minimized_POS.txt': lastResult.humanPOS,
        };
        Object.keys(zipData).forEach(name => {
            const blob = new Blob([zipData[name]], { type: 'text/plain' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a'); a.href = url; a.download = name; a.click(); URL.revokeObjectURL(url);
        });
    }

    // K-map visualizer: produce 2D grid placed by kmapCoords
    function buildKMapGrid() {
        // Safety: ensure table entries exist
        const safeTable = Array.isArray(table) ? table : makeInit(vars);
        // map to objects containing index and coords
        const coords = safeTable.map(r => ({ idx: r?.index ?? 0, coord: kmapCoords(r?.index ?? 0, vars) }));
        let maxR = 0, maxC = 0;
        coords.forEach(({ coord }) => {
            if (!coord || coord.length < 2) return;
            if (coord[0] > maxR) maxR = coord[0];
            if (coord[1] > maxC) maxC = coord[1];
        });
        const rows = maxR + 1;
        const cols = maxC + 1;
        const grid = Array.from({ length: rows }, () => Array.from({ length: cols }, () => null));
        coords.forEach(({ idx, coord }) => {
            if (!coord || coord.length < 2) return;
            const [rr, cc] = coord;
            // store index (integer) in grid, NOT the full row object
            grid[rr][cc] = idx;
        });
        return { grid, rows, cols };
    }

    const { grid, rows, cols } = buildKMapGrid();

    return (
        <div className="p-6 font-sans">
            <h1 className="text-2xl font-bold mb-4">K-Map Minimizer — Interactive Web Simulator (fixed)</h1>

            <div className="mb-4 flex gap-4">
                <label className="flex items-center gap-2">Variables:
                    <select value={vars} onChange={e => {
                        const v = parseInt(e.target.value) || 1;
                        setVars(v);
                    }} className="ml-2">
                        {[1, 2, 3, 4, 5].map(n => <option key={n} value={n}>{n}</option>)}
                    </select>
                </label>

                <button className="px-3 py-1 bg-blue-600 text-white rounded" onClick={() => { setTable(makeInit(vars)); setLastResult(null); }}>Reset Table</button>
                <button className="px-3 py-1 bg-green-600 text-white rounded" onClick={generateKMAndMinimize}>Generate K-Map & Minimize</button>
                <button className="px-3 py-1 bg-gray-600 text-white rounded" onClick={exportFiles}>Download files</button>
            </div>

            <div className="grid grid-cols-2 gap-6">
                <div>
                    <h2 className="font-semibold mb-2">Truth Table</h2>
                    <div className="overflow-auto border rounded p-2">
                        <table className="w-full table-auto text-sm">
                            <thead>
                                <tr className="bg-gray-100"><th>Index</th>{varNames.map(v => <th key={v}>{v}</th>)}<th>Out</th></tr>
                            </thead>
                            <tbody>
                                {Array.isArray(table) ? table.map((row, rowIndex) => {
                                    // Defensive: ensure row object exists
                                    const r = row || { index: rowIndex, val: '0' };
                                    const bits = bin(r.index, vars).split('');
                                    return (
                                        <tr key={r.index} className="odd:bg-white even:bg-gray-50">
                                            <td className="p-1">{r.index} ({bin(r.index, vars)})</td>
                                            {bits.map((b, i) => <td key={i} className="p-1 text-center">{b}</td>)}
                                            <td className="p-1">
                                                <select value={String(r.val ?? '0')} onChange={e => setCell(r.index, e.target.value)}>
                                                    <option value={'0'}>0</option>
                                                    <option value={'1'}>1</option>
                                                    <option value={'x'}>x (don't care)</option>
                                                </select>
                                            </td>
                                        </tr>
                                    );
                                }) : null}
                            </tbody>
                        </table>
                    </div>
                </div>

                <div>
                    <h2 className="font-semibold mb-2">K-Map / Preview</h2>
                    <div className="border rounded p-2 mb-2">
                        <div className="text-sm mb-2">K-Map visualization (Gray ordering)</div>
                        <div style={{ display: 'grid', gridTemplateColumns: `repeat(${Math.max(1, cols)}, 1fr)`, gap: 6 }}>
                            {grid.map((rowArr, rIdx) => (
                                rowArr.map((cellIndex, cIdx) => {
                                    if (cellIndex === null || cellIndex === undefined) {
                                        return <div key={`empty-${rIdx}-${cIdx}`} className="border rounded p-2 text-xs bg-gray-100">—</div>;
                                    }
                                    const rowObj = Array.isArray(table) ? table[cellIndex] : undefined;
                                    // rowObj may be undefined if table was malformed; guard it
                                    const value = rowObj ? String(rowObj.val) : '(?)';
                                    return (
                                        <div key={`${cellIndex}-${rIdx}-${cIdx}`} className="border rounded p-2 text-xs" title={`Index ${cellIndex}`}>
                                            <div className="font-mono">{bin(cellIndex, vars)}</div>
                                            <div className="mt-1 text-sm">Out: {value}</div>
                                        </div>
                                    );
                                })
                            ))}
                        </div>
                    </div>

                    <div>
                        <h3 className="font-medium">Minimization Result</h3>
                        {!lastResult ? <div className="text-sm text-gray-600">No result — click "Generate K-Map & Minimize"</div> : (
                            <div>
                                <div className="mt-2"><strong>SOP (human):</strong> <div className="font-mono bg-gray-50 p-2 rounded mt-1">{lastResult.humanSOP}</div></div>
                                <div className="mt-2"><strong>SOP (code):</strong> <div className="font-mono bg-gray-50 p-2 rounded mt-1">{lastResult.sopCode}</div></div>
                                <div className="mt-2"><strong>POS (human):</strong> <div className="font-mono bg-gray-50 p-2 rounded mt-1">{lastResult.humanPOS}</div></div>
                                <div className="mt-2"><strong>Verilog module</strong><pre className="bg-black text-white p-2 rounded text-xs overflow-auto">{lastResult.verilogModule}</pre></div>
                                <div className="mt-2"><strong>Testbench</strong><pre className="bg-black text-white p-2 rounded text-xs overflow-auto">{lastResult.testbench}</pre></div>
                                <div className="mt-2"><strong>Logic diagram (SVG preview)</strong>
                                    <div className="mt-1" dangerouslySetInnerHTML={{ __html: lastResult.svg }} />
                                </div>
                            </div>
                        )}
                    </div>
                </div>
            </div>

            <footer className="mt-6 text-sm text-gray-600">Tip: set some 'x' entries for don't-cares. This single-file simulator generates downloadable Verilog and a simple visual preview.</footer>
        </div>
    );
}