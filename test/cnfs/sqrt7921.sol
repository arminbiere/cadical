c ---- [ banner ] ------------------------------------------------------------
c 
c CaDiCaL Radically Simplified CDCL SAT Solver
c Version 02d b708271496f7d759e017985a84b04761b572c0e6
c Copyright (c) 2016 Armin Biere, JKU
c 
c Wed Nov  9 13:01:54 CET 2016
c g++ (Ubuntu 5.4.0-6ubuntu1~16.04.2) 5.4.0 20160609
c Linux fmvi7ab 4.4.0-38-generic x86_64
c g++ -Wall -O3
c 
c ---- [ parsing input ] -----------------------------------------------------
c 
c reading DIMACS file from 'cnfs/sqrt7921.cnf'
c opening file to read 'cnfs/sqrt7921.cnf'
c found 'p cnf 302 839' header
c initialized 302 variables
c parsed 839 clauses in 0.00 seconds
c closing file 'cnfs/sqrt7921.cnf'
c after reading 9762 bytes 0.0 MB
c 
c ---- [ options ] -----------------------------------------------------------
c 
c --arena=3
c --binary=true
c --check=true
c --clim=-1
c --dlim=-1
c --elim=true
c --elimclslim=1000
c --elimignore=0
c --eliminit=1000
c --elimint=10000
c --elimocclim=100
c --elimroundsinit=5
c --elimrounds=2
c --emabumplast=1e-05
c --emagluefast=0.03
c --emaglueslow=1e-05
c --emajump=1e-05
c --emarestarteff=0.001
c --emarestartint=1e-05
c --emasize=1e-05
c --keepglue=2
c --keepsize=3
c --leak=true
c --minimize=true
c --minimizedepth=1000
c --prefetch=true
c --profile=2
c --quiet=false
c --reduce=true
c --reduceglue=true
c --reduceinc=300
c --reduceinit=2000
c --restart=true
c --restartint=4
c --restartmargin=1.1
c --reusetrail=true
c --shrink=true
c --shrinkdepth=2
c --shrinkglue=5
c --shrinksize=20
c --strengthen=true
c --sublast=5
c --subsume=true
c --subsumeinc=10000
c --subsumeinit=10000
c --subsumeocclim=100
c --trailbump=true
c --trailbumplast=40
c --trailbumprops=200
c --verbose=false
c --witness=true
c 
c ---- [ proof tracing ] -----------------------------------------------------
c 
c opening file to write 'cnfs/sqrt7921.proof'
c writing binary DRAT proof trace to 'cnfs/sqrt7921.proof'
c 
c ---- [ solving ] -----------------------------------------------------------
c 
c
c  seconds    reductions      redundant    irredundant     restarteff      propdec
c         MB       restarts           glue       variables      restartint     propconf
c           level       conflicts         size        remaining        bumplast
c
c 1  0.00  0  2.0  0    0     2     2 3.0  9.5  838 252 83.4% 0.00  0.0 20.2% 87 218
c 
c ---- [ closing proof ] -----------------------------------------------------
c 
c closing file 'cnfs/sqrt7921.proof'
c after writing 228 bytes 0.0 MB
c 
c ---- [ result ] ------------------------------------------------------------
c 
s SATISFIABLE
v 1 -2 -3 4 5 -6 7 -8 -9 -10 11 -12 -13 14 -15 -16 17 -18 19 -20 21 -22 -23 24
v -25 -26 27 -28 -29 30 -31 -32 33 34 -35 -36 37 -38 39 40 -41 -42 43 -44 -45
v 46 -47 -48 49 -50 -51 52 -53 -54 55 56 -57 -58 -59 -60 61 -62 -63 -64 -65 66
v 67 -68 69 -70 -71 72 -73 -74 75 -76 -77 78 -79 -80 81 -82 -83 -84 85 -86 -87
v 88 -89 -90 91 -92 -93 94 95 -96 97 -98 99 100 101 -102 -103 104 -105 -106
v 107 -108 -109 110 -111 -112 113 114 -115 -116 -117 118 -119 -120 121 -122
v -123 124 -125 -126 127 -128 -129 130 -131 -132 -133 134 -135 136 -137 138
v 139 -140 141 142 -143 144 -145 -146 147 -148 -149 150 -151 -152 -153 154 155
v -156 -157 -158 -159 160 -161 -162 163 -164 -165 166 -167 -168 169 -170 -171
v 172 -173 -174 175 176 -177 178 -179 180 -181 182 -183 184 -185 -186 187 -188
v -189 190 -191 -192 -193 194 195 -196 -197 -198 199 -200 -201 202 -203 -204
v 205 -206 -207 208 -209 -210 211 -212 213 214 215 -216 -217 218 219 -220 -221
v 222 -223 -224 225 -226 -227 228 229 -230 -231 -232 233 -234 -235 236 -237
v -238 -239 240 -241 -242 243 244 245 246 -247 248 -249 -250 251 252 -253 -254
v -255 256 -257 -258 259 -260 -261 -262 263 -264 -265 266 267 -268 269 -270
v -271 -272 273 -274 -275 276 -277 -278 279 -280 -281 282 283 284 -285 -286
v 287 -288 -289 290 291 292 293 294 295 296 297 298 299 300 301 302
v 0
c 
c ---- [ run-time profiling data ] -------------------------------------------
c 
c         0.00    0.00% collect
c         0.00    0.00% elim
c         0.00    0.00% parse
c         0.00    0.00% reduce
c         0.00    0.00% search
c         0.00    0.00% simplify
c         0.00    0.00% subsume
c   ===============================
c         0.00  100.00% all
c 
c ---- [ statistics ] --------------------------------------------------------
c 
c eliminations:                0         0.00    conflicts per elimination
c subsumptions:                0         0.00    conflicts per subsumption
c reductions:                  0         0.00    conflicts per reduction
c restarts:                    0         0.00    conflicts per restart
c conflicts:                   2         0.00    per second
c decisions:                   5         0.00    per second
c propagations:              437         0.00    millions per second
c reused:                      0         0.00 %  per restart
c resolved:                    0         0.00    per eliminated
c eliminated:                  0         0.00 %  of all variables
c fixed:                      50        16.56 %  of all variables
c units:                       0         0.00    conflicts per unit
c binaries:                    0         0.00    conflicts per binary
c trailbumped:                 0         0.00 %  per conflict
c analyzed:                    2         1.00    per conflict
c learned:                    19         9.50    per conflict
c minimized:                   4        17.39 %  of 1st-UIP-literals
c forward:                     0         0.00    tried per forward
c strengthened:                0         0.00    per forward
c shrunken:                    0         0.00 %  of tried literals
c backward:                    0         0.00 %  per conflict
c searched:                   10         2.00    per decision
c bumped:                    405       202.50    per conflict
c reduced:                     0         0.00 %  clauses per conflict
c collections:                 0         0.00    conflicts per collection
c collected:                   0         0.00    bytes and MB
c maxbytes:               120166         0.11    bytes and MB
c time:                                  0.00    seconds
c 
c exit 10
