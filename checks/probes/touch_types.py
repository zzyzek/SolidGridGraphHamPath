# SPDX-License-Identifier: CC0-1.0
# Enumerate geometric touch types between an even strip a (direction t, cells c_0..c_{k+1})
# and a strip z of the same factor (non-chain, any direction, length >= 1) whose cell w shares
# a side e with a cell v of a, w not in a. A type is (role of v, side of v, role of w, z's
# direction relative to a) consistent with both patterns on e, and with the degree-2
# condition at the two ends of e when it can be decided from the two patterns alone.
#
# Roles in a strip of length n: 0 = start (if n >= 2), interior even, interior odd, end.
# Pattern (direction s): back dark iff role even (start/even) or end of odd length >= 3,
# lats dark iff odd index, front dark iff (odd index and not last) or (even index and last).
def strip_sides(idx, n):
  # membership of back, front, lat for cell index idx in a strip of length n
  lat = idx % 2 == 1
  front = (idx % 2 == 1) == (idx + 1 < n)
  if idx == 0: back = True
  else:
    j = idx - 1
    back = (j % 2 == 1) == (j + 1 < n)
  return back, front, lat
ROLES_A = {'start': 0, 'even': 2, 'odd': 1, 'end': None}
out = set()
for k in (2, 4, 6):
  n = k + 2
  for vname, vi in (('start', 0), ('even', 2), ('odd', 1), ('odd_pre', k - 1), ('even_last', k), ('end', k + 1)):
    if vi is None or vi >= n: continue
    b, f, l = strip_sides(vi, n)
    for vside, dark in (('back', b), ('front', f), ('lat', l)):
      if vname != 'start' and vside == 'back': continue  # shared with previous cell of a
      if vside == 'front' and vname != 'end': continue    # shared with next cell of a
      # z's cell w across that side; z direction relative to a: 'par' (same axis) or 'perp'
      for zn in (1, 2, 3, 4, 5):
        for wi in range(zn):
          zb, zf, zl = strip_sides(wi, zn)
          for zrel in ('par_same', 'par_opp', 'perp_toward', 'perp_away'):
            # which side of w is e?
            if vside == 'lat':
              # e is a lateral side of v; for z parallel it is a lateral side of w;
              # for z perpendicular it is w's back (z moving away) or front (toward)
              wside = 'lat' if zrel.startswith('par') else ('back' if zrel == 'perp_away' else 'front')
            else:
              # e is a back/front side of v (perpendicular to a's axis)
              wside = ('front' if (vside == 'back') == (zrel == 'par_same') else 'back') if zrel.startswith('par') else 'lat'
            if wside == 'front' and wi + 1 < zn: continue   # then the next cell of z is v
            if wside == 'back' and wi > 0: continue          # previous cell of z is v
            wdark = {'back': zb, 'front': zf, 'lat': zl}[wside]
            if wdark != dark: continue
            out.add((vname, vside, 'single' if zn == 1 else ('start' if wi == 0 else ('end' if wi == zn - 1 else ('even' if wi % 2 == 0 else 'odd'))), zrel, wside))
for x in sorted(out): print(x)
print(len(out), 'types')
