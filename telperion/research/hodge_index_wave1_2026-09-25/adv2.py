from adv import *
import sys
for x in [7,8,9]:
    eu=[euler(x,p) for p in (0,1)]; b=[box(x,p) for p in (0,1)]
    print(f'x={x}: box {b[0]:+.3e}/{b[1]:+.3e} euler-adv {eu[0][1]:+.3e}/{eu[1][1]:+.3e}  angles odd {[(p,round(t,2)) for p,t in eu[1][2].items() if t is not None]}',flush=True)
