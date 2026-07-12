from pathlib import Path

path = Path('ErdosProblems/Erdos23GapGBTwoDefectFinal.lean')
text = path.read_text()
old = '''/-- A size-two component of span two is a doubled diamond vertex together
with one tip.  The doubled vertex is on level `l+1` and the tip on `l+2`. -/
set_option maxHeartbeats 800000 in
theorem IsGeodesic.pair_spanTwo_geometry
'''
new = '''set_option maxHeartbeats 800000 in
/-- The local shortest-path extraction below traverses component-complement
quotients, so this isolated theorem needs a larger elaboration budget. -/
theorem IsGeodesic.pair_spanTwo_geometry
'''
if old in text:
    text = text.replace(old, new, 1)
elif new not in text:
    raise SystemExit('expected heartbeat block not found')
path.write_text(text)
