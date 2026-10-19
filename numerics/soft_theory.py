"""Soft-curb closed forms and the hypotheses of the soft one- and two-manoeuvre results.

Tyre model: body-aligned rectangles of half-length lam centred at u = 0 (rear) and u = d_w
(front); outer sidewall at |v| = T_o = w/2 - ds.  Key points: Z = P - lam e - T_o n (outer rear
corner of the curb-side rear tyre) and F' = P + (d_w + lam) e - T_o n (outer front corner of the
curb-side front tyre).
"""
import numpy as np
from scipy.optimize import brentq

DS, LAM = 0.0275, 0.25        # sidewall inset and tyre half-length [m]


def quantities(df, dw, db, w, th, mfrac=0.1, ds=DS, lam=LAM):
    R = dw / np.tan(th); b = dw + df; ell = b + db; Rm, Rp = R - w / 2, R + w / 2
    rho = np.hypot(b, Rp); m = mfrac * w; H = m + w; To = w / 2 - ds; a = dw + lam
    gam = np.arctan2(Rp, b)
    X = lambda p: db * np.cos(p) - Rm * np.sin(p)
    Y = lambda p: Rm * np.cos(p) - b * np.sin(p)
    tilt = lambda A: brentq(lambda p: A * np.sin(p) + (w - ds) * np.cos(p) - H, 0, np.arctan(A / (w - ds)))
    q = dict(R=R, b=b, ell=ell, Rm=Rm, Rp=Rp, rho=rho, m=m, H=H, To=To, a=a, gam=gam)
    q['psi_t'] = tilt(b + lam)                   # nose-up parked tilt bound
    q['psi_tp'] = tilt(db + a)                   # nose-down parked tilt bound
    q['psi_max'] = max(q['psi_t'], q['psi_tp'])
    q['r_t'] = np.hypot(lam, R + To)
    q['beta_t'] = np.arctan2(lam, R + To)
    q['psi_bs'] = np.arcsin((H + ds) / (b + lam))
    q['psi_ns'] = np.arcsin((H + ds) / a)
    q['psi_us'] = brentq(lambda p: (R - To) * (1 - np.cos(p)) + lam * np.sin(p) - (H + ds), 1e-9, np.pi / 2)
    q['eta'] = (df - lam) * np.sin(gam) + ds
    pt = q['psi_t']
    q['L1s'] = X(pt) + np.sqrt(rho**2 - Y(pt)**2)
    q['L1_rigid_classical'] = db + np.sqrt(b * b + 2 * R * w)
    # reverse-exit bound
    h0 = H - (w - ds) * np.cos(q['psi_max']); h1 = H * a / (a + db)
    F = lambda z: np.sqrt(a * a - z * z) - a * np.log((a + np.sqrt(a * a - z * z)) / z)
    fb = lambda p: db * np.cos(p) - (w / 2) * np.sin(p)
    q['h0'], q['h1'] = h0, h1
    q['Bback_s'] = (b * np.cos(pt) - (w / 2) * np.sin(pt) + min(fb(-q['psi_ns']), fb(q['psi_us']))
                    + R / (R + To) * (F(h1) - F(h0)))
    # two manoeuvres (double contact)
    al = np.arccos(R / rho) - np.arctan2(b, Rp)
    q['alpha_s'] = al
    q['L2s'] = b + db * np.cos(al) + Rp * np.sin(al)
    q['tyre_end_two'] = m + w / 2 - R - lam * np.sin(al) + (R - To) * np.cos(al)
    q['RC_end_two'] = m + w / 2 - R - db * np.sin(al) + Rm * np.cos(al)
    C1y = H + 2 * R * np.cos(al) - Rp
    q['psi_max'] = pm = max(q['psi_t'], q['psi_tp'])
    q['Bback_s'] = (b * np.cos(pm) - (w / 2) * np.sin(pm) + min(fb(-q['psi_ns']), fb(q['psi_us']))
                    + R / (R + To) * (F(h1) - F(h0)))
    q['RC_parked'] = -(db - lam) * np.sin(pt) - ds * np.cos(pt)
    q['dip_outer'] = (H + Y(pt)) - q['r_t']          # C_y - r_t at q_t (negative: corner dips)
    ck = {}
    ck['S1 db<b, lam<=min(db,df), ds>=0'] = db < b and lam <= min(db, df) and ds >= 0
    ck['S2 H+ds < min(b+lam, db+a)'] = H + ds < min(b + lam, db + a)
    ck['S2 psi_max < gamma'] = pm < gam
    ck['S2 (w-ds)cos pmax - max(db,df) sin pmax > m'] = (w - ds) * np.cos(pm) - max(db, df) * np.sin(pm) > m
    ck['S2 (w-ds) cos psi_bs > m'] = (w - ds) * np.cos(q['psi_bs']) > m
    ck['S2 Rp cos psi_t > Rm'] = Rp * np.cos(pt) > Rm
    ck['S2 Rm >= db tan(psi_tp/2), Rm tan psi_tp < b'] = Rm >= db * np.tan(q['psi_tp'] / 2) and Rm * np.tan(q['psi_tp']) < b
    ck['S2 r_t cos(psi_max+beta_t) >= H'] = q['r_t'] * np.cos(pm + q['beta_t']) >= H
    ck['S2 H+ds < lam + R - To'] = H + ds < lam + R - To
    ck['S2 h0 < h1'] = h0 < h1
    ck['S3 2Rb > w rho'] = 2 * R * b > w * rho
    ck['S3 m rho + (df-lam) Rp < (w-ds) b'] = m * rho + (df - lam) * Rp < (w - ds) * b
    ck['S3 b rho > (H+eta) Rp'] = b * rho > (H + q['eta']) * Rp
    ck['S4 lam <= (H+Y(psi_t)) sin psi_t'] = lam <= (H + Y(pt)) * np.sin(pt)
    ck['S5 cos psi_t sqrt(b^2+2Rw) > Rm sin psi_t + b'] = np.cos(pt) * np.sqrt(b * b + 2 * R * w) > Rm * np.sin(pt) + b
    ck['S6 Y(psi_t) >= db'] = Y(pt) >= db
    ck['S7 db cos psi_max - Rp sin psi_max + rho >= L1s'] = db * np.cos(pm) - Rp * np.sin(pm) + rho >= q['L1s']
    ck['S7 Bback_s >= L1s'] = q['Bback_s'] >= q['L1s']
    ck['T1 db<b, b tan alpha < Rm'] = db < b and b * np.tan(al) < Rm
    ck['T2 tyre above curb at end of reverse arc'] = q['tyre_end_two'] >= 0
    ck['T3 2R cos a - Rp >= db, lam <= C1y sin a'] = (2 * R * np.cos(al) - Rp >= db) and lam <= C1y * np.sin(al)
    # soft margin condition for the asymptotics: w - (m+ds) sec psi > ell tan(psi/2) on (0, psi_max]
    ps = np.linspace(1e-6, pm, 2000)
    ck['M mcond-s'] = bool(np.all(w - (m + ds) / np.cos(ps) > ell * np.tan(ps / 2)))
    return q, ck


CARS = [("City car", 0.65, 2.35, 0.55, 1.65, 37), ("Compact", 0.85, 2.60, 0.75, 1.78, 36),
        ("Typical", 0.90, 2.60, 0.80, 1.80, 35), ("Mid-size sedan", 0.95, 2.85, 1.00, 1.84, 34),
        ("Large SUV", 1.00, 3.00, 1.05, 1.98, 33), ("Van", 1.00, 3.40, 1.10, 2.00, 31)]

if __name__ == "__main__":
    for name, df, dw, db, w, thd in CARS:
        q, ck = quantities(df, dw, db, w, np.radians(thd))
        bad = [k for k, v in ck.items() if not v]
        print(f"{name:15s} psi_t={q['psi_t']:.5f} psi_tp={q['psi_tp']:.5f} L1s={q['L1s']:.4f} Bback_s={q['Bback_s']:.3f}"
              f" alpha_s={q['alpha_s']:.4f} L2s={q['L2s']:.4f} tyre_end={100*q['tyre_end_two']:.1f}cm"
              f" RC_end={100*q['RC_end_two']:.1f}cm RC_parked={100*q['RC_parked']:.1f}cm dip={1000*q['dip_outer']:.3f}mm failed: {bad}")
    q, ck = quantities(0.9, 2.6, 0.8, 1.8, np.radians(35))
    print({k: round(float(v), 5) for k, v in q.items()})
    print('sensitivity of L1s (typical car):')
    for ds in (0.0, 0.0275, 0.05):
        for lam in (0.20, 0.25, 0.30):
            qq, cc = quantities(0.9, 2.6, 0.8, 1.8, np.radians(35), ds=ds, lam=lam)
            print(f'  ds={ds:.4f} lam={lam:.2f}: L1s={qq["L1s"]:.4f} L2s={qq["L2s"]:.4f} thm hyp ok: {all(v for k,v in cc.items() if k.startswith("S"))}')
