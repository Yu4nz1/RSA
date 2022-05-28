### RSALib-cve漏洞

ROCA：不能正确生成RSA密钥对，这可能使攻击者可以恢复与该库生成的RSA公钥相对应的RSA私钥

漏洞CVE ID：CVE-2017-15361

https://crocs.fi.muni.cz/public/papers/rsa_ccs17

这篇讲的十分详细，且易懂，且此漏洞最先由该团队率先发现，并揭露

https://github.com/nsacyber/Detect-CVE-2017-15361-TPM

GitHub上的官方的总结

一个实现RSA密钥对生成时产生的一个安全漏洞

其算法特征在于所生成的RSA素数的特定结构，1204或2048bit的常用密钥长度的因式分解存在可分解。该漏洞使得攻击者仅知道公共密钥，就能访问易受攻击的设备。

解决措施：可才受影响的设备上使用其他加密算法代替RSA，如ECC（ECC密钥不受此影响）

因此可考虑使用新的ECC密钥对来代替RSA密钥对。

​         若用RSA密钥对，则可以使用其他方式产生RSA密钥对

​         不影响3936bit的密钥长度，512-704,992-1216,1984-2144bit的密钥长度范围实际上是可分解的。

注意：漏洞只影响RSA密钥的生成，而不影响其使用

另，其他团队的攻击：https://blog.cr.yp.to/20171105-infineon.html

其中包括了他们重建攻击的过程

中间涉及逆向工程

我的复现过程：（参考上诉重建过程）

重建过程涉及逆向（在学）

```python
import sympy.ntheory as nt
import random

def prime_default(length=0):
  if length >= 3968:
    return 1427 # real bound 3968
  if length >= 1984:
    return 701 # 701 is used from 1984 rather than 2048
  if length >= 992:
    return 353 # 353 is used from 992 rather than 1024
  if length >= 512:
    return 167
  return 167 # no data for <512, but that doesn't matter anyway

def m_default(length):
  return nt.primorial(prime_default(length), False)

#primorial 质数阶乘
#primorial（n，nth）n –表示要计算其前n个素数或小于或等于n的素数的乘积的数。nth –表示布尔值。为True时，它返回前n个素数的乘积；而当False返回时，它返回小于或等于n的素数的乘积
def gord(x):
  return Zmod(x)(65537).multiplicative_order()

def randpri(g=65537, bits=512, M=None, exact_bits=False):
  if M is None:
    M = m_default(bits)
    
  prime_bits = bits // 2r
  M_bits = log(M, 2r)
  gm = Mod(g, M) # Zmod ring
  gordm = gord(M)
  max_a = gordm - 1r
  min_a = 2r
  ga = random.randint(min_a, max_a)
  u = lift(gm^ga) # g^a mod M, almost always lg(M) bits in size
  g_start = floor(prime_bits - M_bits) - 1
  gk_start = 2 ** g_start
  gk_end = 2 ** (g_start+1)

  while True:
    gk = random.randint(gk_start, gk_end)
    w = M * gk
    gp = w + u
    if exact_bits and prime_bits != round(log(gp, 2)):
      continue
    if Integer(gp).is_prime(proof=False):
      # print('gk: 0x%x\nga: 0x%x\ngp: 0x%x' % (gk, ga, gp))
      return int(gk), int(ga), int(gp)
    
def roca(bits=2048):
  while True:
  	p_k, p_a, p = randpri(bits=bits, exact_bits=True)
    q_k, q_a, q = randpri(bits=bits, exact_bits=True)
    N = p * q
    n_bits = ceil(log(N, 2))
    if n_bits == bits:
   	  return p, q
# print(roca(2048))

from sage.doctest.util import Timer

ttry = Timer()
t = Timer()
L = 27771430913146044712156219115012732149015337058745243774375474371978395728107173008782747458575903820497344261101333156469136833289328084229401057505005215261077328417649807720533310592783171487952296983742789708502518237023426083874832018749447215424764928016413509553872836856095214672430
L *= 701 # if 701 is included
g = Mod(65537,L)
pmin = 12*2^1020
pmax = 13*2^1020
proof.arithmetic(False) # do not bother proving primality
t.start()
u = lift(g^randrange(L))
while True:
  p = u + randrange(ceil(pmin/L),floor(pmax/L)) * L
  if p.is_prime(): break
print 'time for first prime',t.stop().cputime

t.start()
u = lift(g^randrange(L))
while True:
  q = u + randrange(ceil(pmin/L),floor(pmax/L)) * L
  if q.is_prime(): break
print 'time for second prime',t.stop().cputime
n = p * q
print 'public key',n
smooth,k,H = 41902660800,5,7*2^461
m = 2*k+1
print 'smooth',smooth
print 'multiplicity',k
print 'lattice rank',m
print 'Hbits',H.nbits()
print 'H',H

def lg(x): return log(1.0 * x) / log(2.0)

lggamma = lg(m)/(2.0*k) + lg(2*H)*(m-1.0)/(2.0*k) + lg(n)*((k+1.0)/(2.0*m)-1)
gap = lg(pmin) - lg(n) - lggamma
print 'gap',gap
print 'guaranteed',gap > 0

def smoothorder(l):
  return smooth % Mod(g,l).multiplicative_order() == 0

v = prod(l for l,e in factor(L) if smoothorder(l))
print 'v',v
u = p % v
print 'p residue class',u

ttry.start()
pmin = max(pmin,ceil(n / pmax))
pmax = min(pmax,floor(n / pmin))
pradius = (pmax - pmin) // 2
print 'n-dependent pradius bits',pradius.nbits()

R.<x> = ZZ[]
u += floor((pmin + H * v - u) / v) * v # now pmin-v < u-H*v <= pmin

t.start()
wu = lift(u/Mod(v,n))
f = wu+H*x
fpowers = [f^0]
for j in range(k): fpowers += [fpowers[j] * f]
print 'fpowers time',t.stop().cputime,'bits',[fi.nbits() for fi in fpowers[k].coefficients(sparse=False)]

X = matrix([n])
for i in range(1,k):
  t.start()
  X = X.augment(vector(ZZ,i))
  X = X.stack(vector(ZZ,fpowers[i].coefficients(sparse=False)))
  X = X.LLL(delta=0.3,early_red=True,use_siegel=True)
  print 'miniLLL time',t.stop().cputime,'bits',[[Mji.nbits() for Mji in Mi] for Mi in X]
  X = n * X
t.start()
for i in range(k,m):
  X = X.augment(vector(ZZ,i))
  X = X.stack(vector(ZZ,[0]*(i - k) + (H^(i-k)*fpowers[k]).coefficients(sparse=False)))
X = X.LLL(delta=0.6,early_red=True,use_siegel=True)
print 'bigLLL time',t.stop().cputime,'bits',[[Mji.nbits() for Mji in Mi] for Mi in X]

numLLL = 1
shift1 = matrix([[binomial(j,i) for i in range(m)] for j in range(m)])
shift2 = shift1*shift1
t.start()
factored = false
while True:
  # search u-Hv,...,u+Hv in steps of v
  # i.e. search u+vs with s being -H,...,H
  M0 = X[0]
  Q0 = sum(ZZ(z/H^i)*x^i for i,z in enumerate(M0))
  Qroots = Q0.roots(ring=ZZ)
  for r,multiplicity in Qroots:
    if u+v*r > 0:
      g = gcd(n,u+v*r)
      if g > 1 and g < n:
        if not factored:
          print '----- successful factorization',[g,n/g]
          factored = True # could abort at this point but want to benchmark failure case
  u += 2*H*v
  if u-H*v > pmax: break
  X *= shift2
  X = X.LLL(delta=0.6,early_red=True,use_siegel=True)
  numLLL += 1
  
print 'scan time',t.stop().cputime,'numLLL',numLLL
timetry = ttry.stop().cputime
print 'avgyearsx4',timetry * smooth / (86400 * 365.25)

```

email：

https://blog.cr.yp.to/20171105-infineon4.txt



```python
#Sagemath脚本

from sage.doctest.util import Timer

ttry = Timer()
t = Timer()
L = 27771430913146044712156219115012732149015337058745243774375474371978395728107173008782747458575903820497344261101333156469136833289328084229401057505005215261077328417649807720533310592783171487952296983742789708502518237023426083874832018749447215424764928016413509553872836856095214672430
L *= 701 # if 701 is included
g = Mod(65537,L)
pmin = 12*2^1020
pmax = 13*2^1020
proof.arithmetic(False) # do not bother proving primality

t.start()
u = lift(g^randrange(L))
while True:
 p = u + randrange(ceil(pmin/L),floor(pmax/L)) * L
 if p.is_prime(): break
print 'time for first prime',t.stop().cputime

t.start()
u = lift(g^randrange(L))
while True:
 q = u + randrange(ceil(pmin/L),floor(pmax/L)) * L
 if q.is_prime(): break

print 'time for second prime',t.stop().cputime
n = p * q

print 'public key',n
smooth,k,H = 41902660800,5,7*2^461
m = 2*k+1

print 'smooth',smooth
print 'multiplicity',k
print 'lattice rank',m
print 'Hbits',H.nbits()
print 'H',H

def lg(x): return log(1.0 * x) / log(2.0)
lggamma = lg(m)/(2.0*k) + lg(2*H)*(m-1.0)/(2.0*k) + lg(n)*((k+1.0)/(2.0*m)-1)
gap = lg(pmin) - lg(n) - lggamma
print 'gap',gap
print 'guaranteed',gap > 0

def smoothorder(l):
 return smooth % Mod(g,l).multiplicative_order() == 0

v = prod(l for l,e in factor(L) if smoothorder(l))
print 'v',v

u = p % v
print 'p residue class',u

ttry.start()
pmin = max(pmin,ceil(n / pmax))
pmax = min(pmax,floor(n / pmin))
pradius = (pmax - pmin) // 2
print 'n-dependent pradius bits',pradius.nbits()

R.<x> = ZZ[]
u += floor((pmin + H * v - u) / v) * v
# now pmin-v < u-H*v <= pmin
t.start()
wu = lift(u/Mod(v,n))
f = wu+H*x
fpowers = [f^0]
for j in range(k): fpowers += [fpowers[j] * f]
print 'fpowers time',t.stop().cputime,'bits',[fi.nbits() for fi in fpowers[k].coefficients(sparse=False)]

X = matrix([n])
for i in range(1,k):
 t.start()
 X = X.augment(vector(ZZ,i))
 X = X.stack(vector(ZZ,fpowers[i].coefficients(sparse=False)))
 X = X.LLL(delta=0.3,early_red=True,use_siegel=True)
 print 'miniLLL time',t.stop().cputime,'bits',[[Mji.nbits() for Mji in Mi] for Mi in X]
 X = n * X
 
t.start()
for i in range(k,m):
 X = X.augment(vector(ZZ,i))
 X = X.stack(vector(ZZ,[0]*(i - k) + (H^(i-k)*fpowers[k]).coefficients(sparse=False)))

X = X.LLL(delta=0.6,early_red=True,use_siegel=True)
print 'bigLLL time',t.stop().cputime,'bits',[[Mji.nbits() for Mji in Mi] for Mi in X]

numLLL = 1
shift1 = matrix([[binomial(j,i) for i in range(m)] for j in range(m)])
shift2 = shift1*shift1
t.start()

factored = false
while True:
 # search u-Hv,...,u+Hv in steps of v
 # i.e. search u+vs with s being -H,...,H 
 M0 = X[0] 
 Q0 = sum(ZZ(z/H^i)*x^i for i,z in enumerate(M0))
 Qroots = Q0.roots(ring=ZZ)

 for r,multiplicity in Qroots:
  if u+v*r > 0:
   g = gcd(n,u+v*r)
   if g > 1 and g < n:
if not factored:
 print '----- successful factorization',[g,n/g]
 factored = True
 # could abort at this point but want to benchmark failure case
 u += 2*H*v
 if u-H*v > pmax: break
 X *= shift2
 X = X.LLL(delta=0.6,early_red=True,use_siegel=True)
 numLLL += 1
 
print 'scan time',t.stop().cputime,'numLLL',numLLL
timetry = ttry.stop().cputime
print 'avgyearsx4',timetry * smooth / (86400 * 365.25)
```

mark：
detail：https://blog.cr.yp.to/20171105-infineon1.txt
blog：重建过程https://blog.cr.yp.to/20171105-infineon.html
e-mail/Sage脚本：https://blog.cr.yp.to/20171105-infineon4.txt
需要逆向：https://github.com/crocs-muni/roca/blob/master/roca/detect.py
GKCTF2020的Backdoor：https://asecuritysite.com/encryption/copper（该网站可以跑py脚本，在线的）

该题中的p的生成方式是p=k*M+(65537**a %M)，其中M为前x个质数的乘积（即素数阶乘）
对于512-960bit密钥长度，M为39个素数乘积，理论上只要确定了M，a，k的值并不会太大，直接暴力

>512960bit 39
992-1952bit 71
1984-3936bit 126
1968-4096bit 225

```python
from Crypto.Util import number
from gmpy2 import *

vals=39
M=1
n = mpz(15518961041625074876182404585394098781487141059285455927024321276783831122168745076359780343078011216480587575072479784829258678691739)
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 
2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999]

for x in range(0, vals):
  M=M*primes[x]
for a in range(1,20):
  for k in range(50):
  p=mpz(k*M+(65537**a %M))

if gmpy2.is_prime(p):
  q = mpz(n//p)
  if gmpy2.is_prime(q):
    print('p=%d\nq=%d'%(p,q))
```