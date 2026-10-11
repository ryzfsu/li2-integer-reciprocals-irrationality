#!/usr/bin/env python3
"""Recompute the printed endpoint and signed-family bounds from TeX data."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
import time

import printed_v_data
import p0_engine
import v_engine
from flint import arb, ctx


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def file_sha(path: Path) -> str:
    return sha256(path.read_bytes()).hexdigest()


def input_tree(main: Path) -> tuple[str, dict[str, str]]:
    root = main.parent.resolve()
    seen: dict[str, str] = {}

    def visit(path: Path, active: tuple[Path, ...]) -> str:
        path = path.resolve()
        require(path.is_relative_to(root), f"TeX input escapes source root: {path}")
        require(path not in active, f"cyclic TeX input: {path}")
        raw = path.read_text(encoding="utf-8")
        key = path.relative_to(root).as_posix()
        seen[key] = raw
        uncommented = re.sub(r"(?<!\\)%[^\n]*", "", raw)

        def include(match: re.Match[str]) -> str:
            child = path.parent / match.group(1)
            if not child.suffix:
                child = child.with_suffix(".tex")
            return visit(child, active + (path,))

        expanded = re.sub(r"\\(?:input|include)\s*\{([^}]+)\}", include, uncommented)
        return expanded

    return visit(main, ()), seen


def tex_number(text: str) -> F:
    text = text.strip().replace("$", "")
    m = re.fullmatch(r"\\frac\{(-?\d+)\}\{(\d+)\}", text)
    if m:
        return F(int(m.group(1)), int(m.group(2)))
    return F(text)


def row_value(block: str, label: str) -> str:
    lines = block.splitlines()
    for i, line in enumerate(lines):
        if "&" not in line:
            continue
        left, right = line.split("&", 1)
        if re.sub(r"\\[A-Za-z]+", "", left).strip() != label:
            continue
        values = [right]
        j = i + 1
        while j < len(lines) and lines[j].lstrip().startswith("&"):
            values.append(lines[j].lstrip()[1:])
            j += 1
        return " ".join(values)
    raise AssertionError(f"missing printed row: {label}")


def integer_list(cell: str) -> list[int]:
    cell = re.sub(r"\\[A-Za-z]+", " ", cell)
    return [int(x) for x in re.findall(r"(?<![A-Za-z])\d+", cell)]


def rational_list(cell: str) -> list[F]:
    cell = re.sub(r"\\[,; ]", "", cell)
    cell = cell.replace("$", "")
    return [tex_number(x) for x in re.findall(r"-?\d+(?:/\d+)?", cell)]


def p0_table(main: str, q: int) -> dict:
    label = f"tab:q{q}data"
    start = main.index(r"\label{" + label + "}")
    stop = main.index(r"\bottomrule", start)
    block = main[start:stop]
    den_list = integer_list(row_value(block, "denominator"))
    require(len(den_list) == 1, f"q={q}: denominator row is not unique")
    den = den_list[0]

    pin_raw = row_value(block, "pinned edges")
    edge_part = pin_raw.split("divided by", 1)[0]
    pin_edges_i = integer_list(edge_part)
    divs = integer_list(pin_raw.split("divided by", 1)[1])
    require(len(divs) == 1, f"q={q}: malformed pinned edge denominator")
    pin_edges = [F(x, divs[0]) for x in pin_edges_i]
    freq_edges = rational_list(row_value(block, "frequency edges"))
    pin_mass = integer_list(row_value(block, "pinned masses"))
    freq_mass = integer_list(row_value(block, "frequency masses"))
    contour_prefix = integer_list(row_value(block, "contour pair masses"))

    node_count = 64
    require(len(contour_prefix) <= node_count // 2, f"q={q}: contour prefix too long")
    half = contour_prefix + [0] * (node_count // 2 - len(contour_prefix))
    contour_mass = half + list(reversed(half))

    g = re.search(r"\(\\xi,A,B\)=\\left\((.*?)\\right\)", main, re.S)
    require(g is not None, "missing printed P0 ellipse geometry")
    geom = re.findall(r"\\frac\{(-?\d+)\}\{(\d+)\}", g.group(1))
    require(len(geom) == 3, "P0 ellipse geometry must contain three exact fractions")
    geometry = [str(F(int(a), int(b))) for a, b in geom]

    require("64 contour nodes" in main and "Fej\\'er degree 48" in main,
            "missing P0 grid or Fejer degree")
    require(r"\theta_j=\pi(2j+1)/64" in main,
            "missing exact P0 contour angle convention")
    require(r"F_{48}(\theta)=\frac1{49}\left|\sum_{k=0}^{48}e^{ik\theta}\right|^2" in main,
            "missing normalized Fejer kernel definition")
    require(len(pin_edges) == len(pin_mass) + 1 and
            len(freq_edges) == len(freq_mass) + 1,
            f"q={q}: edge/mass count mismatch")
    require(len(contour_prefix) == (9 if q == 2 else 8),
            f"q={q}: contour independent-mass count mismatch")
    require(sum(freq_mass) == den and sum(pin_mass) + sum(contour_mass) == den,
            f"q={q}: exact reference masses do not normalize")
    require(all(x >= 0 for x in pin_mass + freq_mass + contour_mass),
            f"q={q}: negative P0 reference weight")
    require(all(F(w, den) <= b - a for a, b, w in
                zip(pin_edges, pin_edges[1:], pin_mass)),
            f"q={q}: pinned density constraint fails")
    require(all(F(w, den) <= b - a for a, b, w in
                zip(freq_edges, freq_edges[1:], freq_mass)),
            f"q={q}: frequency density constraint fails")
    return {
        "denominator": den,
        "geom": geometry,
        "pinned_edges": [str(x) for x in pin_edges],
        "pinned_mass": pin_mass,
        "frequency_edges": [str(x) for x in freq_edges],
        "frequency_mass": freq_mass,
        "contour_mass": contour_mass,
        "contour_grid_count": node_count,
        "contour_angle_convention": "theta_j=pi(2j+1)/64",
        "contour_density_convention": "sum_j c_j F_48(theta-theta_j)/(2pi)",
        "fejer_degree": 48,
        "exact_nonnegativity": "nonnegative rational weights; F_48 is a squared modulus",
    }


def p0_thresholds(text: str) -> dict[int, tuple[F, F, F]]:
    start = text.index(r"\label{tab:p0-q-bounds}")
    stop = text.index(r"\end{tabular}", start)
    block = text[start:stop]
    result = {}
    for q in (2, 11):
        pattern = (rf"\${q}\$\s*&\s*\$h_\\eta=([^$]+)\$\s*,\s*"
                   rf"\$h_\\mu=([^$]+)\$;.*?Q_\{{\\log\}}>([-0-9.]+)")
        m = re.search(pattern, block, re.S)
        require(m is not None, f"q={q}: missing printed P0 scalar receipt")
        result[q] = (tex_number(m.group(1)), tex_number(m.group(2)), F(m.group(3)))
    return result


def alpha_lower_from_table(text: str, q: int) -> F:
    if q == 2:
        token = r"\alpha(0)\ge\frac{248035}{125000}"
        require(token in text, "q=2: missing printed P0 alpha lower bound")
        return F(248035, 125000)
    token = r"\alpha(\log(11/2))\ge\frac{77597}{100000}"
    require(token in text, "q=11: missing printed P0 alpha lower bound")
    return F(77597, 100000)


def p0_replay(main: str, analytic: str, out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    thresholds = p0_thresholds(analytic)
    result = {}
    ctx.dps = 45
    for q in (2, 11):
        ref = p0_table(main, q)
        c = p0_engine.Certificate(ref, q, False)
        h_eta, h_mu, q_printed_lower = thresholds[q]
        qval, parts = c.Q()
        require(qval.lower() > p0_engine.ar(q_printed_lower),
                f"q={q}: energy lower endpoint misses the printed bound")
        contour = c.contour_check(h_eta, 256, 10, out / f"p0-q{q}-contour.csv")
        P, p_receipt = c.positive_integral(
            c.Wpin, F(1, 4), F(5, 4), h_eta, 8192,
            out / f"p0-q{q}-pinned.csv")
        T, t_receipt = c.positive_integral(
            c.Wfreq, F(1, 2), F(81, 10), h_mu, 16384,
            out / f"p0-q{q}-frequency.csv")
        tail_point = c.Wfreq(p0_engine.ar(F(81, 10)))
        require(tail_point.lower() > p0_engine.ar(h_mu),
                f"q={q}: frequency tail endpoint is below threshold")
        slope = (F(693, 1000) - 1 / (2 * (F(81, 10) - F(1, 2)))
                 + 3 / (F(81, 10) + 2) - 2 / (F(81, 10) - F(9, 2))
                 - 1 / (F(81, 10) - F(751, 5000)))
        require(slope > F(1, 50), f"q={q}: printed tail derivative bound fails")
        lower = c.const + qval + p0_engine.ar(h_eta) + p0_engine.ar(h_mu) - P.upper() - T.upper()
        rat = F(__import__("math").floor(float(lower.lower()) * 10**6) - 1, 10**6)
        require(lower.lower() > p0_engine.ar(rat), f"q={q}: directed alpha flooring failed")
        alpha_table = alpha_lower_from_table(analytic, q)
        require(rat >= alpha_table, f"q={q}: recomputed alpha misses printed lower bound")
        result[str(q)] = {
            "reference_mass_and_density_checks": "PASS",
            "Q_log_interval": str(qval),
            "Q_log_printed_lower": str(q_printed_lower),
            "contour": contour,
            "pinned_positive_part": p_receipt,
            "frequency_positive_part": t_receipt,
            "frequency_tail_endpoint": str(tail_point),
            "frequency_tail_derivative_rational_lower": str(slope),
            "directed_alpha_interval": str(lower),
            "directed_alpha_rational_lower": str(rat),
            "printed_alpha_lower": str(alpha_table),
            "strictly_reproduces_printed_bound": True,
        }
    return result


def v_caps(text: str) -> tuple[dict[int, dict[str, F]], dict[int, F], dict[int, F], dict[int, tuple[int, int, int, int]]]:
    start = text.index(r"\label{tab:v-certificates}")
    stop = text.index(r"\end{tabular}", start)
    block = text[start:stop]
    caps: dict[int, dict[str, F]] = {}
    alpha: dict[int, F] = {}
    q_lower: dict[int, F] = {}
    row_counts: dict[int, tuple[int, int, int, int]] = {}
    for line in block.splitlines():
        m = re.match(
            r"\s*(\d+)\s*&\s*\$([^$]+)\$\s*&\s*\$(-?\d+(?:\.\d+)?)\$\s*"
            r"&\s*\$(-?\d+(?:\.\d+)?)\$\s*&\s*\$(-?\d+(?:\.\d+)?)\$\s*"
            r"&\s*\$>([0-9.]+)\$",
            line,
        )
        if m:
            q = int(m.group(1))
            counts = tuple(int(x) for x in m.group(2).split("/"))
            require(len(counts) == 4, f"q={q}: malformed row-count field")
            row_counts[q] = counts
            caps[q] = {
                "x": tex_number(m.group(3)),
                "v": tex_number(m.group(4)),
                "z": tex_number(m.group(5)),
            }
            alpha[q] = tex_number(m.group(6))
            continue
        # Keep compatibility with the earlier gathered-cell table format.
        m = re.match(r"\s*(\d+)\s*&\s*\$\\begin\{gathered\}(.*?)\\end\{gathered\}\$\s*&\s*\$\\begin\{gathered\}\\alpha>(.*?)\\\\", line)
        if m:
            q = int(m.group(1))
            cvals = [tex_number(x) for x in re.findall(r"-?\d+(?:/\d+|\.\d+)?", m.group(2))]
            require(len(cvals) == 3, f"q={q}: expected three exact printed caps")
            caps[q] = dict(zip(("x", "v", "z"), cvals))
            aval = re.sub(r"\\(?:[-\[\]()0-9a-zA-Z]+)?", "", m.group(3)).strip()
            alpha[q] = tex_number(aval)
    require(set(caps) == set(range(2, 8)) and set(alpha) == set(range(2, 8)),
            "V reference table does not contain exactly q=2,...,7")
    require(set(row_counts) == set(range(2, 8)),
            "V certificate table does not print row counts for q=2,...,7")
    start = text.index(r"\label{tab:v-energy-lower}")
    stop = text.index(r"\end{tabular}", start)
    block = text[start:stop]
    for line in block.splitlines():
        m = re.match(r"\s*(\d+)\s*&\s*\$>(-?\d+(?:\.\d+)?)\$", line)
        if m:
            q_lower[int(m.group(1))] = tex_number(m.group(2))
    require(set(q_lower) == set(range(2, 8)),
            "V energy table does not contain exactly q=2,...,7")
    return caps, alpha, q_lower, row_counts


def v_endpoint_bounds(text: str) -> dict[int, dict[str, F]]:
    start = text.index(r"\label{tab:v-transfer-constants}")
    stop = text.index(r"\end{tabular}", start)
    block = text[start:stop]
    result: dict[int, dict[str, F]] = {}
    for line in block.splitlines():
        m = re.match(
            r"\s*(\d+)\s*&\s*\$([^$]+)\$\s*&\s*\$([^$]+)\$\s*&\s*\$([^$]+)\$\s*&\s*\$([^$]+)\$",
            line,
        )
        if not m:
            continue
        q = int(m.group(1))
        result[q] = {"x": tex_number(m.group(2)), "v": tex_number(m.group(3)),
                     "sigma": tex_number(m.group(4)), "path": tex_number(m.group(5))}
    require(set(result) == set(range(2, 8)),
            "V transfer table does not contain endpoint bounds for q=2,...,7")
    return result


def ceil_sqrt_fraction(value: F) -> int:
    require(value >= 0, "square-root ceiling received a negative rational")
    quotient = value.numerator // value.denominator
    root = __import__("math").isqrt(quotient)
    if root * root * value.denominator < value.numerator:
        root += 1
    return root


def v_transfer_replay(q: int, xrows, yrows, zrows, prows,
                      printed: dict[str, F]) -> dict:
    delta, radius = F(1, 250), F(3, 5)
    hx = max(w / (b - a) for _, a, b, w in xrows)
    hv = max(w / (b - a) for _, a, b, w in yrows)
    hz = max(w / (b - a) for _, a, b, w in zrows)
    scale = 1 << 120
    poisson_density = F(0)
    poisson_radii = []
    for _, cr, ci, mass in prows:
        rho = F(ceil_sqrt_fraction((cr * cr + ci * ci) * scale * scale), scale)
        require(rho < radius, f"q={q}: outward Poisson radius is not inside the circle")
        poisson_radii.append(rho)
        poisson_density += mass * (radius + rho) / (radius * (radius - rho))
    ax, av, az = 2 * hx, 2 * hv, 2 * hz + poisson_density
    bx, bv, bz = 6 * ax + 2, 6 * av + F(5, 2), 6 * az + 2
    sigma = 2 * bx + F(7, 2) * bv + F(13, 4) * bz
    sigma_up = F((sigma.numerator * 1000 + sigma.denominator - 1) // sigma.denominator,
                 1000)

    def integral_log_plus(rows, negative=False):
        total = arb(0)
        for _, a, b, mass in rows:
            lo, hi = (-b, -a) if negative else (a, b)
            lo, hi = lo + delta, hi + delta
            L, R = v_engine.A(lo), v_engine.A(hi)
            primitive_l = L * (L.log() - 1)
            primitive_r = R * (R.log() - 1)
            total += v_engine.A(mass) * (primitive_r - primitive_l) / v_engine.A(b - a)
        return total

    jx = integral_log_plus(xrows)
    jv = integral_log_plus(yrows)
    jz = integral_log_plus(zrows, negative=True)
    jz += sum((v_engine.A(mass) * v_engine.A(radius + delta).log()
               for _, cr, ci, mass in prows), arb(0))
    ex = 2 * jx - v_engine.A(F(5, 4)) * v_engine.A(F(q) - delta).log() \
         + v_engine.A(F(3, 4)) * v_engine.A(delta).log()
    ev = 2 * jv + jz - v_engine.A(F(q) - delta).log() \
         + v_engine.A(F(1, 4)) * v_engine.A(delta).log()
    path = (v_engine.A(F(q + 1) - 2 * radius)
            + v_engine.A(radius)
            * (v_engine.arb.pi() ** 2 + v_engine.A(q).log() ** 2).sqrt())

    require(v_engine.A(printed["x"]).lower() > ex.upper(),
            f"q={q}: printed E_x is not an outward upper bound")
    require(v_engine.A(printed["v"]).lower() > ev.upper(),
            f"q={q}: printed E_v is not an outward upper bound")
    require(printed["sigma"] == sigma_up,
            f"q={q}: printed Sigma is not the exact upward 10^-3 rounding")
    require(v_engine.A(printed["path"]).lower() > path.upper(),
            f"q={q}: printed path bound is not an outward upper bound")
    return {
        "H_x": str(hx), "H_v": str(hv), "H_z": str(hz),
        "Poisson_density_sum_exact": str(poisson_density),
        "outward_Poisson_radii": [str(x) for x in poisson_radii],
        "A_x": str(ax), "A_v": str(av), "A_z": str(az),
        "B_x": str(bx), "B_v": str(bv), "B_z": str(bz),
        "Sigma_exact": str(sigma), "Sigma_printed_upward": str(sigma_up),
        "E_x_recomputed_interval": str(ex), "E_x_printed_upper": str(printed["x"]),
        "E_v_recomputed_interval": str(ev), "E_v_printed_upper": str(printed["v"]),
        "path_recomputed_interval": str(path), "path_printed_upper": str(printed["path"]),
        "strictly_recomputed": True,
    }


def v_reference(tex: str, q: int) -> dict:
    rows = printed_v_data.decode_rows(tex)
    data = {}
    for name, support in (("x", "x"), ("y", "y"), ("z_real", "z_real")):
        data[name] = [dict(a=str(a), b=str(b), w=str(w))
                      for _, a, b, w in rows[(q, support)]]
    data["z_poisson"] = [dict(re=str(a), im=str(b), w=str(w))
                         for _, a, b, w in rows[(q, "z_poisson")]]
    return data


def v_replay(vref: str, vana: str, out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    caps, alpha_printed, q_lower_printed, printed_rows = v_caps(vana)
    endpoint_bounds = v_endpoint_bounds(vana)
    rows = printed_v_data.decode_rows(vref)
    summary = {}
    for q in range(2, 8):
        xrows = rows[(q, "x")]
        yrows = rows[(q, "y")]
        zrows = rows[(q, "z_real")]
        prows = rows[(q, "z_poisson")]
        actual_rows = (len(xrows), len(yrows), len(zrows), len(prows))
        require(actual_rows == printed_rows[q],
                f"q={q}: decoded row counts {actual_rows} != printed {printed_rows[q]}")
        require(all(a < b and w >= 0 for _, a, b, w in xrows + yrows + zrows),
                f"q={q}: nonpositive interval length or negative interval mass")
        require(all(0 <= a < b <= 1 for _, a, b, w in xrows + yrows),
                f"q={q}: x or v interval leaves [0,1]")
        require(all((-q <= a < b <= -F(3, 5)) for _, a, b, w in zrows),
                f"q={q}: real z interval leaves [-q,-3/5]")
        for support_rows in (xrows, yrows, zrows):
            require(all(support_rows[i][2] == support_rows[i + 1][1]
                        for i in range(len(support_rows) - 1)),
                    f"q={q}: interval rows are not a contiguous chain")
        require(xrows[0][1] > 0 and yrows[0][1] > 0 and
                zrows[0][1] == -q and zrows[-1][2] == -F(3, 5),
                f"q={q}: printed chain endpoints are inconsistent")
        require(all(w >= 0 for _, cr, ci, w in prows),
                f"q={q}: negative Poisson mass")
        require(all(prows[i][1] == prows[-1-i][1]
                    and prows[i][2] == -prows[-1-i][2]
                    and prows[i][3] == prows[-1-i][3]
                    for i in range(len(prows) - 1)),
                f"q={q}: Poisson rows are not conjugate symmetric")
        require(sum((w for _, a, b, w in xrows), F(0)) == 1,
                f"q={q}: x mass mismatch")
        require(sum((w for _, a, b, w in yrows), F(0)) == F(5, 4),
                f"q={q}: v mass mismatch")
        require(sum((w for _, a, b, w in zrows), F(0)) +
                sum((w for _, a, b, w in prows), F(0)) == 1,
                f"q={q}: z mass mismatch")
        require(all(a < b for _, a, b, w in xrows + yrows + zrows),
                f"q={q}: degenerate interval")
        require(all(a*a + b*b < F(9, 25) for _, a, b, w in prows),
                f"q={q}: Poisson centre outside the circle")
        data = v_reference(vref, q)
        transfer = v_transfer_replay(q, xrows, yrows, zrows, prows,
                                      endpoint_bounds[q])
        report = v_engine.run_certificate(
            data, q, caps[q], maxdepth=30, endpoint_bounds=endpoint_bounds[q]
        )
        for support, receipt in report["caps"].items():
            require(receipt["strict_pass"], f"q={q} {support}: field bound is not strict")
        ctx.dps = 90
        v_engine.set_reference(data, q, caps[q])
        Q, _ = v_engine.compute_Q()
        require(Q.lower() > v_engine.A(q_lower_printed[q]),
                f"q={q}: recomputed energy misses printed Q lower bound")
        alpha = (Q - arb(F(3, 2).numerator) / F(3, 2).denominator * arb(q).log()
                 - v_engine.A(caps[q]["x"] + F(5, 4) * caps[q]["v"] + caps[q]["z"]))
        require(alpha.lower() > v_engine.A(alpha_printed[q]),
                f"q={q}: recomputed energy and field bounds miss printed alpha lower bound")
        report["alpha_printed_lower"] = str(alpha_printed[q])
        report["Q_printed_lower"] = str(q_lower_printed[q])
        report["alpha_recomputed_interval"] = str(alpha)
        report["alpha_strictly_above_printed"] = True
        report["row_counts_printed_and_recomputed"] = {
            "printed": list(printed_rows[q]), "recomputed": list(actual_rows)}
        report["transfer_constants_recomputed"] = transfer
        summary[str(q)] = report
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tex-root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    main_tex = args.tex_root / "main.tex"
    expanded, sources = input_tree(main_tex)
    ana = (args.tex_root / "chapters/p0-analytic.tex").read_text(encoding="utf-8")
    vana = (args.tex_root / "chapters/v-analytic.tex").read_text(encoding="utf-8")
    vref = (args.tex_root / "chapters/v-reference-data.tex").read_text(encoding="utf-8")
    require("directed upper field interval is finite" in vana,
            "missing printed V cap success rule")
    args.out.mkdir(parents=True, exist_ok=True)
    p0 = p0_replay(expanded, ana, args.out / "p0")
    v = v_replay(vref, vana, args.out / "v")
    report = {
        "status": "PASS",
        "tex_sha256": {k: sha256(v.encode("utf-8")).hexdigest()
                       for k, v in sorted(sources.items())},
        "p0_endpoint_replay": p0,
        "v_fixed_base_replay": v,
        "runtime_seconds": time.monotonic() - start,
        "scope": "Exact printed reference data; directed endpoint and full-support field-bound replay.",
    }
    (args.out / "verification.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"FAIL: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise SystemExit(1)
