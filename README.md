# How long must a parallel-parking space be?

Source of the paper *How long must a parallel-parking space be? Exact one-manoeuvre length,
two-manoeuvre strategies, and sharp many-manoeuvre asymptotics*, with its Lean 4 formalisation
and the numerical code behind its tables and figures.

A car with front-wheel steering is modelled as a rectangle that moves along curves of
curvature at most `1/R`. It has to park between two cars that stand at a margin `m` from the
curb. The paper studies the shortest slot `L_min(n)` that allows parking with at most `n`
manoeuvres. It gives:

- `L_min(1)` in closed form;
- explicit strategies and numerical values for small `n`;
- the sharp asymptotics `L_min(n) = ℓ + K/√n + o(n^{-1/2})`, with `K² = 4Rw − w³/(6R)`;
- a soft-curb variant, in which only the tyres must stay off the curb.

Appendix H of the paper describes how the paper was produced.

## Layout

| Directory | Contents |
|---|---|
| `paper/` | LaTeX source (`main.tex`, `sections/`, `figures/`) and the built `main.pdf` |
| `lean/` | Lean 4 + Mathlib formalisation (see [`lean/README.md`](lean/README.md)) |
| `numerics/` | Python code for all numerical values, tables and figures |
| `numerics/logs/` | logs of the longer runs |
| `numerics/legacy/` | scripts for early versions of the model, before the margin model; not used in the paper |
| `numerics/extra/` | results not in the paper (the 20-manoeuvre motion started 10 cm outside the parked cars) |
| `notes/` | working notes from the development; partly superseded by the paper |

## Paper

```sh
cd paper
pdflatex main.tex && pdflatex main.tex && pdflatex main.tex
```

The bibliography is inline, so no BibTeX run is needed. Standard TeX Live packages are used
(`amsmath`, `mathtools`, `hyperref`, `cleveref`, `enumitem`, `booktabs`, `microtype`, `xcolor`).

## Lean

```sh
cd lean
lake exe cache get              # optional: download Mathlib binaries
lake build                      # library Parking (everything except AsymAxiom)
lake build Parking.AsymAxiom    # the files that use the labelled axiom
```

Lean v4.35.0 and Mathlib v4.35.0. There is no `sorry`; the assumptions and the one labelled
axiom are listed in `lean/README.md` and Section 9 of the paper.

## Numerics

Python 3 with `numpy`, `scipy` and `matplotlib`. The versions used were Python 3.12, numpy 1.26,
scipy 1.11 and matplotlib 3.6.

Run the scripts from `numerics/`. They read and write the `out_*.json` files there; figures go
to `paper/figures/` and tables to `paper/sections/`. Everything is single-threaded. The table
and figure scripts take seconds to minutes. The searches take from minutes to hours.

**Shared modules**

| File | Contents |
|---|---|
| `fast.py` | car model, exact collision test, escape length `V` (rigid curb) |
| `soft.py` | soft-curb collision test (tyres only) and one-manoeuvre search |
| `figtools.py` | drawing and path tools for the multi-manoeuvre figures |
| `assumptions.py` | check of Assumption (A1)–(A7) (Appendix A) |
| `soft_theory.py` | soft-curb closed forms and the hypotheses (S1)–(S7), (T1)–(T3) |
| `car_table.py` | zigzag search and slot lengths for the six cars; writes `out_car_table.json` |
| `twenty_search.py` | contact-zigzag search for 20 manoeuvres; writes `out_twenty.json` |

**Results in the paper**

| Paper | Scripts |
|---|---|
| Table 2 (zigzags) | `opt2.py`–`opt5.py`, `zig_greedy.py` (successive versions of the search; logs in `logs/out_opt*`) |
| Table 3 (crawl) | `wiggle.py` (logs in `logs/out_wiggle_*`) |
| two-manoeuvre searches (Section 5) | `opt_two_fam.py`, `opt_two_broad.py`, `inspect_two.py` |
| checks for Sections 4 and 6 | `alpha_min.py`, `hyp_check.py`, `calib_test.py` |
| Table 6 (other cars) | `car_table.py`, then `car_table_tex.py` |
| Appendix D (20 manoeuvres) | `twenty_search.py`, then `fig_twenty.py` |
| soft-curb values (Sections 7, 8) | `soft_table.py`, `soft_polish.py`, `soft_tight.py`, `soft_five.py` (`soft_runs.py`: an earlier run, used as warm starts) |
| soft-curb checks | `soft_verify.py`, `soft_checks.py`, `soft_sens.py` |
| Table 4, Fig. 8 (comparison) | `compare_tex.py` |
| Figs. 1, 3, 5, 6 | `figures.py` (also writes an older `fig_one.pdf`; run `fig_one.py` afterwards) |
| Fig. 2 | `fig_one.py` |
| Fig. 4 | `fig_values.py` |
| Fig. 7 | `fig_two_soft.py` |
| Figs. 9, 11 | `fig_five.py`, `fig_five.py soft` |
| Figs. 10, 12 | `fig_twenty.py`, `fig_twenty.py soft` |
| not in the paper | `gap_start.py` (start 10 cm outside the parked cars; `fig_twenty.py 0.10 extra/fig_twenty_gap10cm.pdf`) |
