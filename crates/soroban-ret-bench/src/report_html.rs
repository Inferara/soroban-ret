//! Self-contained HTML report: a sortable per-contract restoration table plus a
//! collapsible "what was missed" section per contract. No external assets.

use std::collections::BTreeMap;
use std::fmt::Write;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::diff::{DiffReport, Verdict};
use crate::metrics::{BenchReport, ContractBench, FnStatus};

const STYLE: &str = r#"
:root{color-scheme:light dark;
  --bg:#0f1115;--panel:#171a21;--panel2:#1d212b;--fg:#e6e9ef;--muted:#9aa3b2;
  --line:#2a2f3a;--good:#3fb950;--warn:#d29922;--bad:#f85149;--accent:#58a6ff;}
@media(prefers-color-scheme:light){:root{
  --bg:#f6f8fa;--panel:#fff;--panel2:#f0f3f6;--fg:#1f2328;--muted:#636c76;
  --line:#d0d7de;--good:#1a7f37;--warn:#9a6700;--bad:#cf222e;--accent:#0969da;}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);
  font:14px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
.wrap{max-width:1200px;margin:0 auto;padding:28px 20px 64px}
h1{font-size:22px;margin:0 0 4px}
.sub{color:var(--muted);font-size:13px;margin-bottom:20px}
.hero{display:flex;gap:24px;align-items:center;flex-wrap:wrap;
  background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:18px 22px;margin-bottom:22px}
.big{font-size:42px;font-weight:700;line-height:1}
.big .pct{font-size:22px;color:var(--muted)}
.delta{font-size:15px;font-weight:600}
.kpis{display:flex;gap:22px;flex-wrap:wrap;margin-left:auto}
.kpi{text-align:center}.kpi b{display:block;font-size:20px}.kpi span{color:var(--muted);font-size:12px}
.up{color:var(--good)}.down{color:var(--bad)}.flat{color:var(--muted)}
table{width:100%;border-collapse:collapse;background:var(--panel);
  border:1px solid var(--line);border-radius:12px;overflow:hidden}
th,td{padding:8px 10px;text-align:right;border-bottom:1px solid var(--line);white-space:nowrap}
th:first-child,td:first-child{text-align:left}
thead th{position:sticky;top:0;background:var(--panel2);cursor:pointer;user-select:none;font-size:12px;color:var(--muted)}
thead th:hover{color:var(--fg)}
tbody tr:hover{background:var(--panel2)}
.bar{position:relative;height:16px;width:120px;background:var(--panel2);border-radius:4px;display:inline-block;vertical-align:middle;margin-right:8px;overflow:hidden}
.bar>i{position:absolute;left:0;top:0;bottom:0;border-radius:4px}
.g{background:var(--good)}.a{background:var(--warn)}.r{background:var(--bad)}
.mono{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:12px}
details{background:var(--panel);border:1px solid var(--line);border-radius:10px;margin:10px 0;padding:0 14px}
details[open]{padding-bottom:14px}
summary{cursor:pointer;padding:12px 0;font-weight:600;display:flex;gap:12px;align-items:center}
summary::-webkit-details-marker{display:none}
summary .tag{margin-left:auto;font-weight:400;color:var(--muted);font-size:12px}
.sec{margin:6px 0 2px;font-size:12px;text-transform:uppercase;letter-spacing:.04em;color:var(--muted)}
.badge{display:inline-block;padding:1px 7px;border-radius:999px;font-size:11px;font-weight:600}
.b-clean{background:rgba(63,185,80,.15);color:var(--good)}
.b-partial{background:rgba(210,153,34,.15);color:var(--warn)}
.b-lost{background:rgba(248,81,73,.15);color:var(--bad)}
.b-triv{background:rgba(154,163,178,.15);color:var(--muted)}
.b-miss{background:rgba(248,81,73,.15);color:var(--bad)}
.chips{display:flex;flex-wrap:wrap;gap:6px;margin:4px 0 10px}
.chip{background:var(--panel2);border:1px solid var(--line);border-radius:6px;padding:2px 8px;font-size:12px}
.err{color:var(--bad);font-weight:600}
ul.diag{margin:4px 0 10px;padding-left:18px;color:var(--muted)}
.ftable th,.ftable td{padding:5px 8px;font-size:12px}
footer{color:var(--muted);font-size:12px;margin-top:28px;text-align:center}
"#;

const SCRIPT: &str = r#"
function sortTable(tbl,col){
  var t=document.getElementById(tbl),tb=t.tBodies[0],
      rows=Array.prototype.slice.call(tb.rows),
      dir=t.getAttribute('data-dir-'+col)==='asc'?-1:1;
  t.setAttribute('data-dir-'+col,dir===1?'asc':'desc');
  rows.sort(function(a,b){
    var x=a.cells[col],y=b.cells[col],
        xv=x.dataset.val!==undefined?parseFloat(x.dataset.val):x.textContent.toLowerCase(),
        yv=y.dataset.val!==undefined?parseFloat(y.dataset.val):y.textContent.toLowerCase();
    if(xv<yv)return -dir; if(xv>yv)return dir; return 0;
  });
  rows.forEach(function(r){tb.appendChild(r)});
}
"#;

fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

fn bar_class(pct: f64) -> &'static str {
    if pct >= 80.0 {
        "g"
    } else if pct >= 50.0 {
        "a"
    } else {
        "r"
    }
}

fn status_badge(s: FnStatus) -> &'static str {
    match s {
        FnStatus::Clean => "<span class=\"badge b-clean\">clean</span>",
        FnStatus::Partial => "<span class=\"badge b-partial\">partial</span>",
        FnStatus::LogicLost => "<span class=\"badge b-lost\">logic lost</span>",
        FnStatus::Trivial => "<span class=\"badge b-triv\">trivial</span>",
        FnStatus::Missing => "<span class=\"badge b-miss\">missing</span>",
    }
}

/// Render the full HTML report.
pub fn render(report: &BenchReport, diff: Option<&DiffReport>) -> String {
    let deltas: BTreeMap<&str, &crate::diff::ContractDelta> = diff
        .map(|d| d.deltas.iter().map(|x| (x.file.as_str(), x)).collect())
        .unwrap_or_default();

    let mut o = String::new();
    let _ = write!(
        o,
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\
         <title>soroban-ret restoration benchmark</title><style>{STYLE}</style></head><body><div class=\"wrap\">"
    );

    // Header / hero.
    let _ = write!(
        o,
        "<h1>soroban-ret restoration benchmark</h1>\
         <div class=\"sub\">Corpus <span class=\"mono\">{}</span> · {} contracts · generated {} UTC</div>",
        esc(&report.corpus),
        report.contracts.len(),
        utc_now_string(),
    );

    let _ = write!(
        o,
        "<div class=\"hero\"><div><div class=\"big\">{:.1}<span class=\"pct\">%</span></div>",
        report.overall_restoration
    );
    if let Some(d) = diff {
        let (cls, txt) = delta_span(d.overall_verdict, d.overall_delta);
        let _ = write!(
            o,
            "<div class=\"delta {cls}\">{txt} vs baseline {:.1}%</div>",
            d.overall_baseline
        );
    }
    let _ = write!(o, "</div>");

    // KPIs.
    let clean: usize = report.contracts.iter().map(|c| c.fn_clean).sum();
    let partial: usize = report.contracts.iter().map(|c| c.fn_partial).sum();
    let lost: usize = report.contracts.iter().map(|c| c.fn_logic_lost).sum();
    let artifacts: usize = report.contracts.iter().map(|c| c.artifacts.total).sum();
    let _ = write!(o, "<div class=\"kpis\">");
    for (label, val) in [
        ("clean fns", clean),
        ("partial fns", partial),
        ("lost fns", lost),
        ("artifacts", artifacts),
    ] {
        let _ = write!(
            o,
            "<div class=\"kpi\"><b>{val}</b><span>{label}</span></div>"
        );
    }
    if let Some(d) = diff {
        let _ = write!(
            o,
            "<div class=\"kpi\"><b class=\"up\">{}</b><span>improved</span></div>\
             <div class=\"kpi\"><b class=\"down\">{}</b><span>reduced</span></div>",
            d.improved, d.reduced
        );
    }
    let _ = write!(o, "</div></div>");

    // Summary table.
    render_table(&mut o, report, &deltas, diff.is_some());

    // Per-contract detail sections.
    let _ = write!(
        o,
        "<h2 style=\"font-size:18px;margin:26px 0 6px\">What was missed</h2>"
    );
    for c in &report.contracts {
        render_detail(&mut o, c);
    }

    let _ = write!(
        o,
        "<footer>Reference-free metric — restoration % is the mean per-exported-function \
         recovery (concrete Rust vs. <span class=\"mono\">todo!()</span>/unknown nodes). \
         Disassembly time is informational and excluded from the verdict.</footer>"
    );
    let _ = write!(o, "</div><script>{SCRIPT}</script></body></html>");
    o
}

fn render_table(
    o: &mut String,
    report: &BenchReport,
    deltas: &BTreeMap<&str, &crate::diff::ContractDelta>,
    has_diff: bool,
) {
    let _ = write!(o, "<table id=\"t\" data-dir-1=\"asc\">");
    let _ = write!(o, "<thead><tr>");
    let mut col = 0;
    let mut th = |o: &mut String, name: &str| {
        let _ = write!(o, "<th onclick=\"sortTable('t',{col})\">{name}</th>");
        col += 1;
    };
    th(o, "Contract");
    th(o, "Restoration");
    if has_diff {
        th(o, "Δ");
    }
    th(o, "Spec fns");
    th(o, "Clean");
    th(o, "Partial");
    th(o, "Lost");
    th(o, "Artifacts");
    th(o, "Disasm ms");
    th(o, "Total ms");
    th(o, "Size");
    let _ = write!(o, "</tr></thead><tbody>");

    for c in &report.contracts {
        let label = c.entity.clone().unwrap_or_else(|| c.file.clone());
        let _ = write!(o, "<tr>");
        let _ = write!(
            o,
            "<td data-val=\"{}\"><b>{}</b><br><span class=\"mono\" style=\"color:var(--muted)\">{}</span></td>",
            esc(&label.to_lowercase()),
            esc(&label),
            esc(&c.file)
        );
        if let Some(err) = &c.error {
            let _ = write!(o, "<td data-val=\"-1\" class=\"err\">error</td>",);
            // fill remaining cells minimally
            if has_diff {
                let _ = write!(o, "<td>—</td>");
            }
            let _ = write!(
                o,
                "<td colspan=\"7\" class=\"err\">{}</td><td data-val=\"{}\">{}</td></tr>",
                esc(err),
                c.wasm_size,
                human_size(c.wasm_size)
            );
            continue;
        }
        let cls = bar_class(c.restoration_pct);
        let _ = write!(
            o,
            "<td data-val=\"{0}\"><span class=\"bar\"><i class=\"{1}\" style=\"width:{0}%\"></i></span>{0:.1}%</td>",
            c.restoration_pct, cls
        );
        if has_diff {
            match deltas.get(c.file.as_str()) {
                Some(d) => {
                    let (sc, txt) = delta_span(d.verdict, d.delta);
                    let _ = write!(
                        o,
                        "<td data-val=\"{}\" class=\"{}\">{}</td>",
                        d.delta, sc, txt
                    );
                }
                None => {
                    let _ = write!(o, "<td data-val=\"0\" class=\"flat\">—</td>");
                }
            }
        }
        let _ = write!(
            o,
            "<td data-val=\"{0}\">{0}</td><td data-val=\"{1}\">{1}</td><td data-val=\"{2}\">{2}</td>\
             <td data-val=\"{3}\">{3}</td><td data-val=\"{4}\">{4}</td><td data-val=\"{5}\">{5:.3}</td>\
             <td data-val=\"{6}\">{6:.3}</td><td data-val=\"{7}\">{8}</td></tr>",
            c.spec_functions,
            c.fn_clean,
            c.fn_partial,
            c.fn_logic_lost,
            c.artifacts.total,
            c.disasm_ms,
            c.total_ms,
            c.wasm_size,
            human_size(c.wasm_size),
        );
    }
    let _ = write!(o, "</tbody></table>");
}

fn render_detail(o: &mut String, c: &ContractBench) {
    let label = c.entity.clone().unwrap_or_else(|| c.file.clone());
    let _ = write!(o, "<details><summary>{}", esc(&label));
    if c.error.is_some() {
        let _ = write!(o, " <span class=\"badge b-lost\">error</span>");
    } else {
        let _ = write!(
            o,
            " <span class=\"badge {}\">{:.1}%</span>",
            match bar_class(c.restoration_pct) {
                "g" => "b-clean",
                "a" => "b-partial",
                _ => "b-lost",
            },
            c.restoration_pct
        );
    }
    let _ = write!(
        o,
        "<span class=\"tag\">{} clean · {} partial · {} lost · {} artifacts</span></summary>",
        c.fn_clean, c.fn_partial, c.fn_logic_lost, c.artifacts.total
    );

    // Meta chips.
    let _ = write!(o, "<div class=\"chips\">");
    let _ = write!(o, "<span class=\"chip mono\">{}</span>", esc(&c.file));
    if let Some(id) = &c.contract_id {
        let _ = write!(o, "<span class=\"chip mono\">{}</span>", esc(id));
    }
    let _ = write!(o, "<span class=\"chip\">{}</span>", human_size(c.wasm_size));
    if let Some(v) = &c.sdk_version {
        let _ = write!(o, "<span class=\"chip\">SDK {}</span>", esc(v));
    }
    for i in &c.standard_interfaces {
        let _ = write!(o, "<span class=\"chip\">{}</span>", esc(i));
    }
    let _ = write!(
        o,
        "<span class=\"chip\">disasm {:.3} ms</span><span class=\"chip\">total {:.3} ms</span></div>",
        c.disasm_ms, c.total_ms
    );

    if let Some(err) = &c.error {
        let _ = write!(
            o,
            "<p class=\"err\">Decompilation failed: {}</p></details>",
            esc(err)
        );
        return;
    }

    // Artifact breakdown.
    let a = &c.artifacts;
    let _ = write!(o, "<div class=\"sec\">Artifacts</div><div class=\"chips\">");
    let _ = write!(
        o,
        "<span class=\"chip\">unknown value: {}</span>",
        a.unknown_value
    );
    let _ = write!(o, "<span class=\"chip\">host call: {}</span>", a.host_call);
    let _ = write!(o, "<span class=\"chip\">stub body: {}</span>", a.stub);
    let _ = write!(o, "<span class=\"chip\">var_N: {}</span></div>", a.var_n);

    // Aggregated missing host calls.
    let mut hc: BTreeMap<&str, usize> = BTreeMap::new();
    for f in &c.functions {
        for h in &f.missing_host_calls {
            *hc.entry(h.as_str()).or_default() += 1;
        }
    }
    if !hc.is_empty() {
        let _ = write!(
            o,
            "<div class=\"sec\">Unrecovered host calls</div><div class=\"chips\">"
        );
        let mut pairs: Vec<_> = hc.into_iter().collect();
        pairs.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        for (name, n) in pairs {
            let _ = write!(o, "<span class=\"chip mono\">{} ×{}</span>", esc(name), n);
        }
        let _ = write!(o, "</div>");
    }

    // Diagnostics.
    if !c.diagnostics.is_empty() {
        let _ = write!(
            o,
            "<div class=\"sec\">Validation diagnostics</div><ul class=\"diag\">"
        );
        for d in &c.diagnostics {
            let _ = write!(o, "<li>{}</li>", esc(d));
        }
        let _ = write!(o, "</ul>");
    }

    // Functions needing attention (non-clean first), then the rest.
    let mut fns: Vec<_> = c.functions.iter().collect();
    fns.sort_by(|a, b| {
        a.score
            .partial_cmp(&b.score)
            .unwrap()
            .then(a.name.cmp(&b.name))
    });
    let _ = write!(
        o,
        "<div class=\"sec\">Functions ({})</div><table class=\"ftable\"><thead><tr>\
         <th>Function</th><th>Status</th><th>Recovery</th><th>Nodes</th><th>Missing host calls</th>\
         </tr></thead><tbody>",
        c.functions.len()
    );
    for f in fns {
        let nodes = if f.total_nodes == 0 {
            "—".to_string()
        } else {
            format!("{}/{}", f.total_nodes - f.unknown_nodes, f.total_nodes)
        };
        let _ = write!(
            o,
            "<tr><td class=\"mono\">{}</td><td>{}</td><td>{:.0}%</td><td>{}</td><td class=\"mono\">{}</td></tr>",
            esc(&f.name),
            status_badge(f.status),
            f.score * 100.0,
            nodes,
            esc(&f.missing_host_calls.join(", "))
        );
    }
    let _ = write!(o, "</tbody></table></details>");
}

fn delta_span(v: Verdict, delta: f64) -> (&'static str, String) {
    match v {
        Verdict::Improved => ("up", format!("▲ +{delta:.1}")),
        Verdict::Reduced => ("down", format!("▼ {delta:.1}")),
        Verdict::NoChange => ("flat", "= 0.0".to_string()),
        Verdict::New => ("flat", "✚ new".to_string()),
        Verdict::Removed => ("flat", "✖ removed".to_string()),
    }
}

fn human_size(bytes: usize) -> String {
    if bytes >= 1024 {
        format!("{:.1} KB", bytes as f64 / 1024.0)
    } else {
        format!("{bytes} B")
    }
}

/// UNIX timestamp → `YYYY-MM-DD HH:MM` (UTC), no external crates.
fn utc_now_string() -> String {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0) as i64;
    let days = secs.div_euclid(86_400);
    let rem = secs.rem_euclid(86_400);
    let (h, mi) = (rem / 3600, (rem % 3600) / 60);
    let (y, m, d) = civil_from_days(days);
    format!("{y:04}-{m:02}-{d:02} {h:02}:{mi:02}")
}

/// Howard Hinnant's days-from-civil inverse: days since 1970-01-01 → (y, m, d).
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = (if mp < 10 { mp + 3 } else { mp - 9 }) as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}
