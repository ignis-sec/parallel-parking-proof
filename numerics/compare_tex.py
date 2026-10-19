"""Comparison table (paper/sections/tab_compare.tex) and figure (fig_compare.pdf):
rigid-curb vs soft-curb slot lengths for the six cars, n = 1..5, and n = 20 for the typical car."""
import os
import json
import numpy as np, matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

rig = {r['name']: r for r in json.load(open('out_car_table.json'))}
soft = json.load(open('out_soft_table.json'))
rig20 = json.load(open('out_twenty.json'))['L']
names = ["City car", "Compact", "Typical", "Mid-size sedan", "Large SUV", "Van"]


def soft_val(name, n):
    s = soft[name]
    if n == 1:                                 # exact value where thm:one-soft applies
        return s['L1s_closed'] if s['thm_hyp'] else s['L1']
    if n == 2:
        return min(s['L2'], s['L2s_closed'])
    return s[f'L{n}']


def ceil3(x):
    return np.ceil(x * 1000 - 1e-9) / 1000


def fmt(v, n):
    """Exact values (n = 1) are rounded to nearest, upper bounds (n >= 2) are rounded up."""
    return f"{v:.3f}" if n == 1 else f"{ceil3(v):.3f}"


lines = [r"\begin{table}[ht]", r"\centering\small", r"\begin{tabular}{@{}llccccc@{}}", r"\toprule",
         r"car & curb & $n=1$ & $n=2$ & $n=3$ & $n=4$ & $n=5$\\", r"\midrule"]
gains = {n: [] for n in range(1, 6)}
for name in names:
    r = rig[name]
    rv = [r['L1'], r['L2'], r['L3'], r['L4'], r['L5']]
    sv = [soft_val(name, n) for n in range(1, 6)]
    for n in range(5):
        gains[n + 1].append(rv[n] - sv[n])
    lines.append(f"{name} & rigid & " + " & ".join(fmt(v, n + 1) for n, v in enumerate(rv)) + r"\\")
    lines.append(r" & soft & " + " & ".join(fmt(v, n + 1) for n, v in enumerate(sv)) + r"\\")
    if name != names[-1]:
        lines.append(r"\addlinespace[2pt]")
lines += [r"\bottomrule", r"\end{tabular}",
          r"\caption{Slot lengths (in metres) with a rigid curb (\cref{tab:cars}) and with a soft curb, for margin $m=w/10$ and the tyre data of \cref{sec:model-soft}.",
          r"For $n=1$ the values are exact (\cref{thm:one,thm:one-soft}; for the city car the soft value is numerical).",
          r"For $n=2$ the soft values are $\Lambda_2^{\rm s}$ of \cref{prop:two-soft}; all entries with $n\ge2$ are upper bounds.}",
          r"\label{tab:compare}", r"\end{table}"]
open('../paper/sections/tab_compare.tex', 'w').write("\n".join(lines) + "\n")
for n in range(1, 6):
    g = np.array(gains[n]) * 100
    print(f"n={n}: soft gain {g.min():.1f}-{g.max():.1f} cm (typical {g[2]:.1f})")
for i, name in enumerate(names):
    print(f"  {name:15s} gains [cm]: " + "  ".join(f"{100 * gains[n][i]:5.1f}" for n in range(1, 6)))
print("negative gains:", [(names[i], n) for n in range(1, 6) for i, g in enumerate(gains[n]) if g < 0])

# figure: typical car
plt.rcParams.update({'font.size': 9, 'font.family': 'serif'})
ell, R, w = 4.3, 2.6 / np.tan(np.radians(35)), 1.8
K = np.sqrt(4 * R * w - w**3 / (6 * R))
r = rig['Typical']
rx = [1, 2, 3, 4, 5, 20]
ry = [r['L1'], r['L2'], r['L3'], r['L4'], r['L5'], rig20]
sy = [soft_val('Typical', n) for n in range(1, 6)] + [soft['twenty']['L']]
fig, ax = plt.subplots(figsize=(5.4, 3.3))
ax.axhline(ell, color='0.5', ls=':', lw=0.8)
ax.text(1.05, ell + 0.015, r'$\ell$', color='0.4')
for y, c, mk, lab in ((ry, 'tab:blue', 'o', 'rigid curb'), (sy, 'tab:red', 's', 'soft curb')):
    ax.plot(rx[:5], y[:5], mk + '-', color=c, ms=4, lw=0.8, label=lab)
    ax.plot(rx[4:], y[4:], mk + ':', color=c, ms=4, lw=0.8)      # n = 6..19 not computed
    ax.annotate(f"{np.ceil(y[5] * 1000 - 1e-9) / 1000:.3f}", (rx[5], y[5]), xytext=(4, 4 if c == 'tab:blue' else -10),
                textcoords='offset points', fontsize=7, color=c)
ax.set_xscale('log')
ax.set_xticks([1, 2, 3, 4, 5, 10, 20])
ax.set_xticklabels(['1', '2', '3', '4', '5', '10', '20'])
ax.set_xlabel('number of manoeuvres $n$')
ax.set_ylabel('slot length [m]')
ax.set_ylim(4.2, 6.0)
ax.set_xlim(0.9, 40)
ax.legend(fontsize=8, frameon=False, loc='upper right')
fig.tight_layout()
fig.savefig(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'paper', 'figures', 'fig_compare.pdf'))
print("typical rigid", [round(v, 4) for v in ry], "soft", [round(v, 4) for v in sy])
