import sys, json
exec(open('zeros.py').read().split('if __name__')[0])
a,b,h=float(sys.argv[1]),float(sys.argv[2]),float(sys.argv[3])
t=mp.mpf(a); prev=mp.re(Z('D',t)); n=0
while t<b:
    t+=h; cur=mp.re(Z('D',t))
    if prev*cur<0: n+=1
    prev=cur
z=json.load(open('zeros_D_1200.json'))['zeros']
print('fine count',n,'coarse count',sum(1 for g in z if a<g<b))
