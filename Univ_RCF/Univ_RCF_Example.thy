theory Univ_RCF_Example imports "RCF_Decision_Proc"
begin

(*univ_rcf 0.9s; univ_rcf_cert 0.3s*)
lemma example_1:
    "\<forall>x::real. \<not>(x>=-9 \<and> x<10 \<and> x^4>0) \<or> x^12>0"
by univ_rcf


(*univ_rcf 1.4s; univ_rcf_cert 0.6s*)
lemma example_2:
    "\<forall>x::real. \<not>((x-2)^2 * (-x+4)>0 \<and> x^2*(x-3)^2\<ge>0 \<and> x-1 \<ge> 0 \<and> - ((x - 3) ^ 2)+1>0) \<or> (-(x-11/12))^3*(x-41/10)^3\<ge>0 "
by univ_rcf



(*univ_rcf 1.6s; univ_rcf_cert 0.7s*)
lemma example_3:
"\<exists>x::real.
      x^5 - x - 1 = 0
      \<and> 
      x^12 + 425/23*x^11 - 228/23*x^10 - 2*x^8 
      - 896/23*x^7 - 394/23*x^6 + 456/23*x^5 + x^4 
      + 471/23*x^3 + 645/23*x^2 - 31/23*x - 228/23= 0 
      \<and> x^3 + 22*x^2 -31 >=0 
      \<and> x^22 -234/567*x^20 -419*x^10+ 1948>0"
by (univ_rcf_cert "[ALG [:- 1, - 1, 0, 0, 0, 1:] (4781 / 4096) (9563 / 8192)]")

(*univ_rcf 1.3s; univ_rcf_cert 0.5*)
lemma example_4:"
\<forall>(x::real). x > 0 | -((61*x)/9) + (5*x^2)/9 + (20*x^3)/9 > -4 | 1 <= x | x <= 0 | 
  -((19*x)/9) + (10*x^2)/9 <= -1 | -((13*x)/9) + (31*x^2)/45 + x^3/18 <= 
   -(7/10) | -((61*x)/9) + (5*x^2)/9 + (20*x^3)/9 <= -4
"
by univ_rcf


(*univ_rcf 1.6s; univ_rcf_cert 0.6*)
lemma example_5:"
\<forall>(x::real). -((5*x)/6) - (10*x^2)/3 - x^3/3 > 0 | (5*x)/6 + (10*x^2)/3 + x^3/3 > 0 | 
  1 <= x | x <= 0 | -((19*x)/9) + (10*x^2)/9 <= -1 | 
  -((13*x)/9) + (31*x^2)/45 + x^3/18 <= -(7/10) | 
  -((101*x)/30) - (64*x^2)/15 + (14*x^3)/15 <= -(11/5) | 
  -((61*x)/9) + (5*x^2)/9 + (20*x^3)/9 <= -4
"
by univ_rcf

(*univ_rcf 5.6s; univ_rcf_cert 3.9*)
lemma example_6:"\<exists>x::real. -((51*x)/10) - (267*x^2)/2 - (5409*x^3)/10 - (4329*x^4)/5 - (2052*x^5)/5 - 
    70*x^6 > -(7/10) & -((10327*x)/270) - (71681*x^2)/270 - 
    (135853*x^3)/810 - (57328*x^4)/135 + (77743*x^5)/135 + 
    (115774*x^6)/405 + (175*x^7)/18 + (49*x^8)/3 + (49*x^9)/162 > 
   -(721/90) & -((2981*x)/90) - (251*x^2)/6 - (24217*x^3)/270 + 
    (2698*x^4)/135 + (18964*x^5)/135 - (595*x^6)/54 + (280*x^7)/27 + 
    (7*x^8)/27 > -(206/45) & -((799*x)/90) + (169*x^2)/18 - 
    (7933*x^3)/270 + (2672*x^4)/135 + (329*x^5)/90 + (112*x^6)/27 + 
    (7*x^7)/54 > -(103/90) & -((781*x)/90) - (701*x^2)/6 - 
    (12217*x^3)/270 + (11323*x^4)/135 + (7264*x^5)/135 + (935*x^6)/54 + 
    (280*x^7)/27 + (7*x^8)/27 > -(77/15) & 
  -((361*x)/30) - (811*x^2)/30 + (307*x^3)/45 + (2353*x^4)/90 - 
    (17*x^5)/6 + (52*x^6)/9 + (2*x^7)/9 > -(44/15) & 
  -((33*x)/10) - (2*x^2)/15 + (41*x^3)/90 + (2*x^4)/15 + 2*x^5 + x^6/9 > 
   -(11/15) & -((1339*x)/405) - (70225*x^2)/324 - (11549*x^3)/270 + 
    (65378*x^4)/405 + (23483*x^5)/810 + (1109*x^6)/27 + (1540*x^7)/81 + 
    (49*x^8)/162 > -(721/60) & -((10741*x)/540) - (2263*x^2)/45 + 
    (5191*x^3)/180 + (7753*x^4)/270 - (52*x^5)/9 + (203*x^6)/18 + 
    (7*x^7)/27 > -(103/15) & -((1481*x)/90) - (811*x^2)/180 + 
    (2113*x^3)/90 - (493*x^4)/36 + (59*x^5)/9 + (2*x^6)/9 > -(22/5) & 
  -((913*x)/180) + (563*x^2)/90 - (257*x^3)/60 + (17*x^4)/9 + x^5/9 > 
   -(11/10) & -((91*x)/18) + (10*x^2)/3 - (5*x^3)/2 + (20*x^4)/9 > -2 & 
  -((2*x)/9) - (25*x^2)/18 + (10*x^3)/9 > -(1/2) & 
  -((61*x)/9) + (5*x^2)/9 + (20*x^3)/9 > -4 & 1 > x & x > 0 & 
  -((19*x)/9) + (10*x^2)/9 > -1 & -((13*x)/9) + (31*x^2)/45 + x^3/18 > 
   -(7/10) & -((253*x)/90) - (53*x^2)/30 + (34*x^3)/15 + x^4/9 > 
   -(11/5) & -((97*x)/90) - (2051*x^2)/90 + (86*x^3)/15 + (82*x^4)/9 + 
    (2*x^5)/9 > -(44/5) & -((93307*x)/1620) - (298609*x^2)/810 + 
    (30583*x^3)/270 + (264373*x^4)/810 - (289811*x^5)/1620 + 
    (3113*x^6)/27 + (931*x^7)/81 + (8*x^8)/81 > -(193/5) & 
  -((4741*x)/540) - (9151*x^2)/90 + (6397*x^3)/60 - (2686*x^4)/135 + 
    (28*x^5)/9 + (38*x^6)/3 + (7*x^7)/27 > -(77/10)
"
by (univ_rcf_cert "[RAT (1 / 32)]")


(*univ_rcf 38.4s; univ_rcf_cert 34.9*)
lemma example_7:"
\<forall>x::real. x < -1 | 0 > x | (41613*x)/2 + 26169*x^2 + (64405*x^3)/4 + 4983*x^4 + 
    (7083*x^5)/10 + (1207*x^6)/35 + x^7/8 > -6435 | 
  11821609800*x + 22461058620*x^2 + 35*x^12 <= 
   4171407240*x^3 + 45938678170*x^4 + 54212099480*x^5 + 31842714428*x^6 + 
    10317027768*x^7 + 1758662439*x^8 + 144537452*x^9 + 5263834*x^10 + 
    46204*x^11 | x <= 0 | 9609600*x + 45805760*x^2 + 92372280*x^3 + 
    102560612*x^4 + 68338600*x^5 + 27930066*x^6 + 6857016*x^7 + 
    938908*x^8 + 58568*x^9 + 753*x^10 <= 0 | 
  788107320*x + 1101329460*x^2 + 10*x^11 <= 
   782617220*x^3 + 2625491260*x^4 + 2362290448*x^5 + 1063536663*x^6 + 
    240283734*x^7 + 24397102*x^8 + 1061504*x^9 + 9179*x^10 | 
  90935460*x + 81290790*x^2 + 5*x^10 <= 125595120*x^3 + 237512625*x^4 + 
    161529144*x^5 + 51834563*x^6 + 6846880*x^7 + 356071*x^8 + 2828*x^9 | 
  640640*x + 2735040*x^2 + 4837448*x^3 + 4581220*x^4 + 2505504*x^5 + 
    794964*x^6 + 138652*x^7 + 11237*x^8 + 207*x^9 <= 0 | 
  5*x^8 <= 73920*x + 238560*x^2 + 303324*x^3 + 192458*x^4 + 63520*x^5 + 
    10261*x^6 + 608*x^7 | 73920*x + 278880*x^2 + 424284*x^3 + 
    332962*x^4 + 142928*x^5 + 32711*x^6 + 3514*x^7 + 98*x^8 <= 0 | x <= -1
"
by univ_rcf

end
