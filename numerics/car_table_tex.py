"""Write the appendix table (paper/sections/tab_cars.tex) from out_car_table.json."""
import json

rows = json.load(open("out_car_table.json"))


def closed(r):
    return r.get("L2_closed", r.get("L2_hyp", False) and r.get("L2_sim", False))


def f3(x):
    return "---" if x is None else f"{x:.3f}"


def c3(x):
    """Upper bounds are rounded up."""
    import math
    return "---" if x is None else f"{math.ceil(x * 1000 - 1e-9) / 1000:.3f}"


def f2(x):
    return f"{x:.2f}"


lines = [
    r"\begin{table}[ht]",
    r"\centering\small",
    r"\setlength{\tabcolsep}{4pt}",
    r"\begin{tabular}{@{}l*{5}{c}cc*{5}{c}c@{}}",
    r"\toprule",
    r"& $d_f$ & $d_w$ & $d_b$ & $w$ & $\theta$ & $\ell$ & $R$"
    r" & $n=1$ & $n=2$ & $n=3$ & $n=4$ & $n=5$ & $K$\\",
    r"\midrule",
]
for r in rows:
    lines.append(
        f"{r['name']} & {f2(r['df'])} & {f2(r['dw'])} & {f2(r['db'])} & {f2(r['w'])} & "
        f"${r['theta']}^\\circ$ & {f2(r['ell'])} & {f2(r['R'])} & "
        f"{f3(r['L1'])} & {c3(r['L2'])}{'' if closed(r) else '$^{*}$'} & {c3(r.get('L3'))} & {c3(r.get('L4'))} & "
        f"{c3(r.get('L5'))} & {f2(r['K'])}\\\\")
lines += [
    r"\bottomrule",
    r"\end{tabular}",
    r"\caption{Slot lengths (in metres) for parallel parking with $n$ manoeuvres, for six car"
    r" configurations with margin $m=w/10$.",
    r"The column $n=1$ is the exact value $\Lmin(1)=\Lambda_1$ of \cref{thm:one}.",
    r"The column $n=2$ is $\Lambda_2^*$ from \cref{prop:two-better}; entries marked $^*$ are"
    r" numerical, because there the double contact occurs before the rear corner passes the"
    r" bottom of its circle ($\alpha_1<\beta$, cf.\ \cref{rem:two-other}).",
    r"The columns $n=3,4,5$ are the best rotation zigzags found.",
    r"All entries with $n\ge2$ are upper bounds for $\Lmin(n)$.",
    r"For large $n$, $\Lmin(n)=\ell+K/\sqrt n+o(n^{-1/2})$ by \cref{thm:asym}.}",
    r"\label{tab:cars}",
    r"\end{table}",
]
open("../paper/sections/tab_cars.tex", "w").write("\n".join(lines) + "\n")
for r in rows:
    print(r["name"], all(r["assumptions"].values()), closed(r),
          f3(r["L1"]), f3(r["L2"]), f3(r.get("L3")), f3(r.get("L4")), f3(r.get("L5")))
