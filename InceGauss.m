(* ::Package:: *)

(* ::Title:: *)
(*InceGauss.m package*)


(* ::Section:: *)
(*Begin the package*)


BeginPackage["InceGauss`"];


(* ::Section:: *)
(*Package code*)


(* ::Subsection:: *)
(*Ince polynomials*)


(* ::Text::Initialization:: *)
(*The Ince polynomials are trigonometric polynomials for which the expansion coefficients define a set of finite recurrence relations. These can be written as an eigenvalue equation in terms of a tridiagonal matrix. The eigenvectors and eigenvalues provide us with the expansion coefficient and the eigenvalue of Ince's equation. It is worth noting that the index \[Mu] indicates the ordering of the eigenvalues and is related to the zeros of the function. They are implemented using partial memorization. *)
(*There are two types of solutions:*)


(* ::Text::Initialization:: *)
(*The even solution which is given by an expansion in terms of even or odd cosines. Therefore this solution is further subdivided into even and odd. Note that N and \[Mu] must have the same parity.*)
(*The odd solution which is given by an expansion in terms of even or odd sines. This solution is also further subdivided into even and odd. *)


InceC::usage="InceC[TotN,\[Mu],\[Epsilon],z] gives the even Ince polynomial \!\(\*FormBox[SubscriptBox[\(C\), \(N, \[Mu]\)],
TraditionalForm]\)(z). TotN and \[Mu] must have the same parity and \[Mu]\[GreaterEqual]0. It is defined as a sum of even and odd cosines. ";
InceS::usage="InceS[TotN,\[Mu],\[Epsilon],z] gives the odd Ince polynomial \!\(\*FormBox[SubscriptBox[\(S\), \(N, \[Mu]\)],
TraditionalForm]\)(z). TotN and \[Mu] must have the same parity and \[Mu]>0. It is defined as a sum of even and odd sines. ";


Begin["`Private`"];


InceC[TotN_Integer,\[Mu]_Integer,\[Epsilon]_,z_]:=Block[{zl,j,l,n,tM,eta,A,ip},
InceC[TotN,\[Mu],\[Epsilon],zl_]=If[EvenQ[TotN],
(* TotN Even *)
j=TotN/2;  l=j+1; n=\[Mu]/2 +1;
If[TotN==0,
1,
tM=DiagonalMatrix[Table[\[Epsilon] (j+k),{k,1,l-1}],1]+DiagonalMatrix[Join[{2\[Epsilon] j},Table[\[Epsilon] (j-k),{k,1,l-2}]],-1]+DiagonalMatrix[Join[{0},Table[4 (k+1)^2,{k,0,l-2}]]];
{eta,A}=SortBy[Eigensystem[tM]\[Transpose],First]\[Transpose];
ip=Plus@@(Table[Cos[(2k)zl],{k,0,l-1}]A[[n]]);
Sign[Plus@@A[[n]]]ip /Sqrt[A[[n]].A[[n]]]],
(* TotN Odd *)
j=(TotN-1)/2;  l=j+1; n=(\[Mu]+1)/2 ;
tM=DiagonalMatrix[Table[\[Epsilon]/2 (TotN+(2k+3)),{k,0,l-2}],1]+DiagonalMatrix[Table[\[Epsilon] /2 (TotN-(2k-1)),{k,1,l-1}],-1]+DiagonalMatrix[Join[{\[Epsilon]/2 (1+TotN)+1},Table[ (2k+1)^2,{k,1,l-1}]]];
{eta,A}=SortBy[Eigensystem[tM]\[Transpose],First]\[Transpose];
ip=Plus@@(Table[Cos[(2k+1)zl],{k,0,l-1}]A[[n]]);
Sign[Plus@@A[[n]]]ip /Sqrt[A[[n]].A[[n]]]
]//Simplify;
InceC[TotN,\[Mu],\[Epsilon],z]
]

InceS[TotN_Integer,\[Mu]_Integer,\[Epsilon]_,z_]:=Block[{zl,j,l,n,tM,eta,A,ip},
InceS[TotN,\[Mu],\[Epsilon],zl_]=
If[EvenQ[TotN],
(* TotN Even *)
j=TotN/2;  l=j+1; n=\[Mu]/2 ;
tM=DiagonalMatrix[Table[\[Epsilon] (j+k),{k,2,l-1}],1]+DiagonalMatrix[Table[\[Epsilon] (j-k),{k,1,l-2}],-1]+DiagonalMatrix[Table[4 (k+1)^2,{k,0,l-2}]];
{eta,A}=SortBy[Eigensystem[tM]\[Transpose],First]\[Transpose];
ip=Plus@@(Table[Sin[(2k)zl],{k,1,l-1}]A[[n]]);
Sign[Plus@@(Table[k,{k,1,l-1}]A[[n]])]ip /Sqrt[A[[n]].A[[n]]],
(* TotN Odd *)
j=(TotN-1)/2;  l=j+1; n=(\[Mu]+1)/2 ;
tM=DiagonalMatrix[Table[\[Epsilon]/2 (TotN+(2k+3)),{k,0,l-2}],1]+DiagonalMatrix[Table[\[Epsilon] /2 (TotN-(2k-1)),{k,1,l-1}],-1]+DiagonalMatrix[Join[{-(\[Epsilon]/2)(1+TotN)+1},Table[ (2k+1)^2,{k,1,l-1}]]];
{eta,A}=SortBy[Eigensystem[tM]\[Transpose],First]\[Transpose];
ip=Plus@@(Table[Sin[(2k+1)zl],{k,0,l-1}]A[[n]]);
Sign[Plus@@(Table[2 k+1,{k,0,l-1}]A[[n]])]ip /Sqrt[A[[n]].A[[n]]]
]//Simplify;
InceS[TotN,\[Mu],\[Epsilon],zl]
]


End[];


(* ::Subsection:: *)
(*Spectrum*)


(* ::Text::Initialization:: *)
(*The Ince equation is an eigenvalue problem for which the Ince polynomials are a solution. The following functions compute the eigenvalues \!\(\*SubsuperscriptBox[\(a\), \(N, \[Mu]\), \((p)\)]\) for each of the eigenfunctions as define by \!\( *)
(*\*SubsuperscriptBox[\(K\), \(N, \[Mu]\), \((p)\)]''\)+\[Epsilon] sin(2z)\!\( *)
(*\*SubsuperscriptBox[\(K\), \(n, \[Mu]\), \((p)\)]'\)+(\!\( *)
(*\*SubsuperscriptBox[\(a\), \(N, \[Mu]\), \((p)\)] - \(N\[Epsilon]\ \(cos(2  z)\)\)\))\!\(\*SubsuperscriptBox[\(K\), \(N, \[Mu]\), \((p)\)]\)=0, where \!\(\*SubsuperscriptBox[\(K\), \(N, \[Mu]\), \((p)\)]\) is equal to Subscript[C, N,\[Mu]] for p=e and to Subscript[S, N,\[Mu]] for p=o.*)
(**)


SpectrumC::usage="SpectrumC[TotN,\[Epsilon]] gives the spectrum of the even Ince polynomial of total order TotN. They are ordered from lowest to highest.";
SpectrumS::usage="SpectrumS[TotN,\[Epsilon]] gives the odd Ince polynomial. TotN and \[Mu] must have the same parity and \[Mu]>0. It is defined as a sum of even and odd sines. ";
IncePolynomialEigenvalue::usage="IncePolynomialEigenvalue[parity,TotN,\[Mu],\[Epsilon]] computes the eigenvalue of the Ince polynomial \!\(\*FormBox[SubscriptBox[\(C\), \(N, \[Mu]\)],
TraditionalForm]\) if parity=\"e\" or \!\(\*FormBox[\(\*SubscriptBox[\(S\), \(N, \[Mu]\)]\\\ if\\\ parity = \*\"\\\\\\\"\" o \*\"\\\\\\\"\"\),
TraditionalForm]\)."


Begin["`Private`"];


(* ::Input::Initialization:: *)
SpectrumC[TotN_Integer,\[Epsilon]_]:=SpectrumC[TotN,\[Epsilon]]=Block[{j,l,tM},
If[EvenQ[TotN],
(* TotN Even *)
j=TotN/2;  l=j+1;
tM=DiagonalMatrix[Table[\[Epsilon] (j+k),{k,1,l-1}],1]+DiagonalMatrix[Join[{2\[Epsilon] j},Table[\[Epsilon] (j-k),{k,1,l-2}]],-1]+DiagonalMatrix[Join[{0},Table[4 (k+1)^2,{k,0,l-2}]]];
Sort[Eigenvalues[tM]],
(* TotN Odd *)
j=(TotN-1)/2;  l=j+1;
tM=DiagonalMatrix[Table[\[Epsilon]/2 (TotN+(2k+3)),{k,0,l-2}],1]+DiagonalMatrix[Table[\[Epsilon] /2 (TotN-(2k-1)),{k,1,l-1}],-1]+DiagonalMatrix[Join[{\[Epsilon]/2 (1+TotN)+1},Table[ (2k+1)^2,{k,1,l-1}]]];
Sort[Eigenvalues[tM]]
]
]


(* ::Input::Initialization:: *)
SpectrumS[TotN_Integer,\[Epsilon]_]:=SpectrumS[TotN,\[Epsilon]]=Block[{j,l,tM},
If[EvenQ[TotN],
(* TotN Even *)
j=TotN/2;  l=j+1; 
tM=DiagonalMatrix[Table[\[Epsilon] (j+k),{k,2,l-1}],1]+DiagonalMatrix[Table[\[Epsilon] (j-k),{k,1,l-2}],-1]+DiagonalMatrix[Table[4 (k+1)^2,{k,0,l-2}]];
Sort[Eigenvalues[tM]],
(* TotN Odd *)
j=(TotN-1)/2;  l=j+1; 
tM=DiagonalMatrix[Table[\[Epsilon]/2 (TotN+(2k+3)),{k,0,l-2}],1]+DiagonalMatrix[Table[\[Epsilon] /2 (TotN-(2k-1)),{k,1,l-1}],-1]+DiagonalMatrix[Join[{-(\[Epsilon]/2)(1+TotN)+1},Table[ (2k+1)^2,{k,1,l-1}]]];
Sort[Eigenvalues[tM]]
]
]


(* ::Input::Initialization:: *)
IncePolynomialEigenvalue[parity_,TotN_Integer,\[Mu]_Integer,\[Epsilon]_]:=Which[parity=="e"&&EvenQ[TotN],SpectrumC[TotN,\[Epsilon]][[\[Mu]/2+1]],
parity!="e"&&EvenQ[TotN],SpectrumS[TotN,\[Epsilon]][[\[Mu]/2]],
OddQ[TotN]&&parity=="e",
SpectrumC[TotN,\[Epsilon]][[(\[Mu]+1)/2]],
OddQ[TotN]&&parity!="e",
SpectrumS[TotN,\[Epsilon]][[(\[Mu]+1)/2]]]



End[];


(* ::Subsection:: *)
(*Ince-Gauss beams*)


(* ::Text:: *)
(*Ince-Gauss beams are defined in terms of elliptical coordinates but it is more convenient for plotting and other calculations to use Cartesian coordinates. ,The specific relation between the two coordinate systems depends on the on the semi-focal distance f which is related to the \[Epsilon] parameter used to define the Ince polynomials via \[Epsilon]=2f^2/w^2. Note that for practical purposes the width of the Gaussian is taken equal to one. *)


CartesianToElliptical::usage="CartesianToElliptical[f,x,y] transform the Cartesian coordinates (x,y) into elliptical coordinates (\[Xi],\[Nu]) defined via \!\(\*FormBox[\(x = f\\\ cosh\\\ \[Xi]\\\ cos\\\ \[Nu]\),
TraditionalForm]\) and \!\(\*FormBox[\(y = f\\\ sinh\\\ \[Xi]\\\ sin\\\ \[Nu]\),
TraditionalForm]\), where f is the semi-focal distance.";
InceGauss::usage="InceGauss[parity,tN,\[Mu],\[Epsilon],x,y,z] calculates the Ince-Gauss beam \!\(\*SubsuperscriptBox[\(IG\), \(N, \[Mu]\), \((p)\)]\)(x,y,z) in Cartesian coordinates. Both the width of the Gaussian and the Rayleigh range have been take equal to one, other values can be incorporated through the arguments. InceGauss[parity,tN,\[Mu],\[Epsilon],x,y]=InceGauss[parity,tN,\[Mu],\[Epsilon],x,y,0]"


Begin["`Private`"];


(* ::Input::Initialization:: *)
CartesianToElliptical[f_,x_,y_]:=Block[{zEll},
zEll=ArcCosh[(x+I y)/f];
{Re[ArcCosh[(x+I y)/f]],Piecewise[{{Im[zEll],Im[zEll]>=0},{2\[Pi]+Im[zEll],Im[zEll]<0}}]}]

InceGauss[parity_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_]:=Block[{\[Xi],\[Eta]},
{\[Xi],\[Eta]}=CartesianToElliptical[Sqrt[\[Epsilon]/2],x,y];
If[parity=="e",
(InceC[TotN,\[Mu],\[Epsilon],I \[Xi]])(InceC[TotN,\[Mu],\[Epsilon],\[Eta]]),
(InceS[TotN,\[Mu],\[Epsilon],I \[Xi]])(InceS[TotN,\[Mu],\[Epsilon],\[Eta]])]Exp[-(x^2+y^2)]
]
InceGauss[parity_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_,z_]:=1/Sqrt[1+z^2] InceGauss[parity,TotN,\[Mu],\[Epsilon],x/Sqrt[1+z^2],y/Sqrt[1+z^2]]Exp[I (x^2+y^2)/(z+1/z)]Exp[-I(TotN+1)ArcTan[z]]
InceGauss[parity_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_,0]:=InceGauss[parity,TotN,\[Mu],\[Epsilon],x,y]


End[];


(* ::Subsection:: *)
(*LG beam expansion coefficients *)


(* ::Text:: *)
(*To compute the LG expansion coefficients of the IG beams we diagonalize the equivalent Bose-Hubbard Hamiltonian. Here we include a linear terms that leads to the unbalanced IG beams*)


CoefficientUnIGinLG::usage="CoefficientUnIGinLG[parity,TotN,\[Mu],\[Epsilon],\[Gamma]] gives the LG expansion coefficients of the unbalanced IG beams. The coefficients are ordered from l ranging from -N to N in steps of two in accordances with the labelling of LG beams in terms of the total order N and the azimuthal index l.";
CoefficientIGinLG::usage="CoefficientIGinLG[parity,TotN,\[Mu],\[Epsilon]] gives the LG expansion coefficients of the unbalanced IG beams. The coefficients are ordered from l ranging from -N to N in steps of two in accordances with the labelling of LG beams in terms of the total order N and the azimuthal index l.";


Begin["`Private`"];


CoefficientUnIGinLG[parity_,TotN_,\[Mu]_,\[Epsilon]_,\[Gamma]_]/;(0<=\[Mu]&&EvenQ[TotN+\[Mu]]):=Block[{hamilBH,eigenvecs,n,coefs,\[Alpha],nnext},
hamilBH=DiagonalMatrix[Table[\[Epsilon]/8 Sqrt[(TotN+lp)(TotN-lp+2)],{lp,-TotN+2,TotN,2}],1]+DiagonalMatrix[Table[(lp/2)^2+\[Gamma] lp/2,{lp,-TotN,TotN,2}]]+DiagonalMatrix[Table[\[Epsilon]/8 Sqrt[(TotN-lp)(TotN+lp+2)],{lp,-TotN,TotN-2,2}],-1];
eigenvecs=SortBy[Eigensystem[4hamilBH]\[Transpose],First[N[#]]&]\[Transpose][[2]];
(*n=If[EvenQ[TotN],If[parity\[Equal]"e",\[Mu]+1,\[Mu]],If[parity\[Equal]"e",\[Mu]+1,\[Mu]]];
coefs=eigenvecs[[n]];
If[Last[coefs]<0,-coefs,coefs]*)
{n,nnext}=If[parity=="e",{\[Mu]+1,\[Mu]},{\[Mu],\[Mu]+1}];
coefs=eigenvecs[[n]];
If[Round[Abs[coefs[[1]]/coefs[[-1]]]]!= 1,
\[Alpha]=(coefs[[1]]-coefs[[-1]])/(coefs[[1]]+coefs[[-1]]);
coefs=coefs-\[Alpha] eigenvecs[[nnext]];
coefs = coefs/Norm[coefs]
];
If[Last[coefs]<0,-coefs,coefs]
]
CoefficientIGinLG[parity_,TotN_,\[Mu]_,\[Epsilon]_]:=CoefficientUnIGinLG[parity,TotN,\[Mu],\[Epsilon],0]


End[];


(* ::Subsection:: *)
(*Helical IG beams*)


(* ::Text:: *)
(*These are constructed by superimposing the IG beam with the same indices but opposite parity.*)


HelicalInceGauss::usage="HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y,z] calculates the helical IG beam \!\(\*SubsuperscriptBox[\(IG\), \(N, \[Mu]\), \((\[PlusMinus])\)]\)(x,y,z). Note that it is not defined for \[Mu]=0. HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y]=HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y,0] ";

CoefficientHelicalIGinLG::usage="CoefficientHelicalIGinLG[sign,TotN,\[Mu],\[Epsilon]] gives the LG expansion coefficients of the helical IG beams. The coefficients are ordered from l ranging from -N to N in steps of two in accordances with the labelling of LG beams in terms of the total order N and the azimuthal index l.";


Begin["`Private`"];


HelicalInceGauss[sign_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_]/;(0<\[Mu]&&EvenQ[TotN+\[Mu]]):=(InceGauss["e",TotN,\[Mu],\[Epsilon],x,y]+Sign[sign]I InceGauss["o",TotN,\[Mu],\[Epsilon],x,y])/Sqrt[2]
HelicalInceGauss[sign_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_,z_]/;(0<\[Mu]&&EvenQ[TotN+\[Mu]]):=(InceGauss["e",TotN,\[Mu],\[Epsilon],x,y,z]+Sign[sign]I InceGauss["o",TotN,\[Mu],\[Epsilon],x,y,z])/Sqrt[2]
HelicalInceGauss[sign_,TotN_,\[Mu]_,\[Epsilon]_,x_,y_,0]:=HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y]

CoefficientHelicalIGinLG[sign_,TotN_,\[Mu]_,\[Epsilon]_]/;(0<\[Mu]&&EvenQ[TotN+\[Mu]]):=(CoefficientIGinLG["e",TotN,\[Mu],\[Epsilon]]+ Sign[sign]CoefficientIGinLG["o",TotN,\[Mu],\[Epsilon]])/Sqrt[2]


End[];


(* ::Subsection:: *)
(*Coherent states*)


(* ::Text:: *)
(*We define the coherent states using their expression in terms of Hermite polynomials and Jones vector, as well as providing their expansion coefficients in terms of Laguerre-Gauss beams.*)


(*RotationCoefs::usage = "RotationCoefs[\[Phi],\[Theta],\[Chi],coeflist] transform the expansion coefficients in terms of LG beams of SG beam according to a rotation of the Majorana constellation. These are astigamtic transfomration parametrized in terms of Euler angles: a rotation around z of \[Chi] followed by a rotation of \[Theta] around y and finshed by a second rotation around z of \[Phi]. ";*)
JonesV::usage = "JonesV[\[Theta],\[Phi]]"
CoherentSG::usage = "CoherentSG[TotN,\[Theta],\[Phi],x,y]"
CoefficientCoherentSGinLG::usage = "CoefficientCoherentSGinLG[TotN,\[Theta],\[Phi]]"


Begin["`Private`"];


JonesV[\[Theta]_,\[Phi]_]:=Cos[\[Theta]/2]Exp[-I \[Phi]/2]{1,I}/Sqrt[2]+Sin[\[Theta]/2]Exp[I \[Phi]/2]{1,-I}/Sqrt[2]
CoherentSG[TotN_,\[Theta]_,\[Phi]_,x_,y_]:=(Sin[\[Theta]])^(TotN/2)/Sqrt[2^(TotN-1) \[Pi] TotN!] Exp[-(x^2+y^2)]HermiteH[TotN,(Sqrt[2]JonesV[\[Theta],\[Phi]].{x,y})/Sqrt[Sin[\[Theta]]]]

RotationCoefs[\[Phi]_,\[Theta]_,\[Chi]_,coeflist_]:=Block[{totN},totN=Length[coeflist]-1;
Table[coeflist.Table[WignerD[{totN/2,lp/2,l/2},\[Theta]]Exp[-I l \[Phi]/2]Exp[-I lp \[Chi]/2],{lp,-totN,totN,2}],{l,-totN,totN,2}]
]

CoefficientCoherentSGinLG[TotN_,\[Theta]_,\[Phi]_]:=RotationCoefs[\[Phi],\[Theta],0.,Append[ConstantArray[0,TotN],1]];


End[];


(* ::Subsection:: *)
(*Semiclassical eigenvalues*)


(* ::Text:: *)
(*Define the functions for computing the semiclassical value for the eigenvalue using the quantization condition of the Poincar\[EAcute] path.*)


\[CapitalDelta]LbyTwoPiE::usage="\[CapitalDelta]LbyTwoPiE[\[Epsilon]n,an] calculates the helical IG beam \!\(\*SubsuperscriptBox[\(IG\), \(N, \[Mu]\), \((\[PlusMinus])\)]\)(x,y,z). Note that it is not defined for \[Mu]=0. HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y]=HelicalInceGauss[sign,TotN,\[Mu],\[Epsilon],x,y,0] ";
GetSemiRcLGregime::usage=""
GetSemiRcHGregime::usage=""


Begin["`Private`"];


\[CapitalDelta]LbyTwoPiE[\[Epsilon]n_,an_?NumericQ]:=Block[{c,r},
c=\[Epsilon]n/2;r=Sqrt[1+c^2-an];
If[c^2+1<an,1,Chop[2 NIntegrate[Sqrt[(1+c Cos[\[Eta]\[Eta]])^2-r^2],{\[Eta]\[Eta],0,If[r+c<1,Pi,ArcCos[(r-1)/c]]}]/(2 Pi)]]]

GetSemiRcLGregime[TotN_,\[Mu]_,\[Epsilon]_]:=Block[{anSemi,R,c},
c=\[Epsilon]/(2(TotN+1));
(*anSemi =a/(N+1)*)
anSemi = Quiet[a/.First[NSolve[\[CapitalDelta]LbyTwoPiE[\[Epsilon]/(TotN+1),a]==\[Mu]/(TotN+1),a]]];
R =If[NumberQ[anSemi]&&anSemi<=1+c^2,Sqrt[1+c^2-anSemi],Message[GetSemiRcLGregime::Rnc];Sqrt[1+c^2-anSemi]];
If[R+c<1,{R,c},Message[GetSemiRcLGregime::Rnc]]
]
GetSemiRcHGregime[parity_,TotN_,\[Mu]_,\[Epsilon]_]:=Block[{anSemi,R,c},
c=\[Epsilon]/(2(TotN+1));

(*anSemi =a/(N+1)*)
anSemi=Quiet[a/.First[NSolve[\[CapitalDelta]LbyTwoPiE[\[Epsilon]/(TotN+1),a]==(If[parity=="o",\[Mu]-1,\[Mu]]+.5)/(TotN+1),a]]];
R =If[NumberQ[anSemi]&&anSemi<=1+c^2,Sqrt[1+c^2-anSemi],Message[GetSemiRcHGregime::Rnc];Sqrt[1+c^2-anSemi]];
If[R+c>1,{R,c},Message[GetSemiRcHGregime::Rnc]]
]

GetSemiRcHGregime::Rnc = "Could not find a combination that was consistent with the chosen regime."
GetSemiRcLGregime::Rnc = "Could not find a combination that was consistent with the chosen regime."


End[];


(* ::Subsection:: *)
(*Parametrization of the Poincar\[EAcute] path*)


PeriodPP::usage=""
SamplingPP::usage=""


Begin["`Private`"];


PeriodPP[c_,R_]:=Block[{\[CurlyPhi]0},
\[CurlyPhi]0=If[R+c>1,ArcCos[(1-c^2-R^2)/(2R c)],0];
If[R+c>1,2,1]NIntegrate[1/Sqrt[1-c^2-R^2-2c R Cos[x]],{x,\[CurlyPhi]0,2\[Pi]-\[CurlyPhi]0}]
]

SamplingPP[c_,R_,sign_]:=Block[{\[Eta]0,tcoord},
If[Abs[c-R]>1,Message[ SamplingPP::nointer]];
\[Eta]0=PeriodPP[c,R];
tcoord=NDSolve[{t1'[\[Eta]]==-t2[\[Eta]]t3[\[Eta]],t2'[\[Eta]]==t1[\[Eta]]t3[\[Eta]]-c t3[\[Eta]],t3'[\[Eta]]==c t2[\[Eta]],t1[0]==c-R,t2[0]==0,t3[0]==sign Sqrt[1-(c-R)^2]},{t1,t2,t3},{\[Eta],0,\[Eta]0}];
{\[Eta]0,tcoord}
]

SamplingPP::nointer = "The values provided for R and c do not form a Poincar\[EAcute] path, i.e. the cylinder and sphere do not intersect."


End[];


(* ::Subsection:: *)
(*Semiclassical estimates: the ray Ince-Gauss beams*)


CoherentStateDecompositionRayIG::usage=""
CoefficientRayIGinLG::usage=""
RayInceGauss::usage=""


Begin["`Private`"];


CoherentStateDecompositionRayIG[parsign_,TotN_,\[Mu]_,\[Epsilon]_,regime_,Mpts_:10]:=Block[{R,c,sign,period,tcoord,st1,st2,st3,jac,jacsqrt,phase\[CapitalUpsilon],\[Eta]step},
{R,c}=Which[regime=="LG",GetSemiRcLGregime[TotN,\[Mu],\[Epsilon]],regime=="HG",GetSemiRcHGregime[parsign,TotN,\[Mu],\[Epsilon]]];
sign=If[regime=="LG",parsign,1];
{period,tcoord}=SamplingPP[c,R,sign];
{st1[\[Eta]_],st2[\[Eta]_],st3[\[Eta]_]}={t1[\[Eta]],t2[\[Eta]],t3[\[Eta]]}/.First[tcoord];
jac[\[Eta]_]:=((1-st3[\[Eta]]^2-c st1[\[Eta]])st3[\[Eta]]+I c st2[\[Eta]])/Sqrt[1-st3[\[Eta]]^2];
jacsqrt[\[Eta]_]:=If[Abs[Arg[jac[period/2]]]<0.1,Sqrt[jac[\[Eta]]],Sqrt[Abs[jac[\[Eta]]]]Exp[I Mod[Arg[jac[\[Eta]]],2\[Pi]]/2]];
phase\[CapitalUpsilon][\[Eta]_]:=NIntegrate[((1-st3[\[Xi]]^2-c st1[\[Xi]])st3[\[Xi]]^2)/(1-st3[\[Xi]]^2),{\[Xi],0,\[Eta]}]/2;
\[Eta]step=period/Mpts;
Table[{jacsqrt[\[Eta]]Exp[I (TotN+1)phase\[CapitalUpsilon][\[Eta]]],{ArcCos[st3[\[Eta]]],Mod[ArcTan[st1[\[Eta]],st2[\[Eta]]],2\[Pi]]}},{\[Eta],\[Eta]step/2,period-\[Eta]step/2,\[Eta]step}]
]

CoefficientRayIGinLG[parsign_,TotN_,\[Mu]_,\[Epsilon]_,regime_,Mpts_:10]:=Block[{coherentList},
coherentList = CoherentStateDecompositionRayIG[parsign,TotN,\[Mu],\[Epsilon],regime,Mpts];
MapThread[(#1 CoefficientCoherentSGinLG[TotN,#2[[1]],#2[[2]]])&,Transpose[coherentList]]//Total
]

RayInceGauss[parsign_,TotN_,\[Mu]_,\[Epsilon]_,regime_,x_,y_,Mpts_:10]:=Block[{coherentList},
coherentList = CoherentStateDecompositionRayIG[parsign,TotN,\[Mu],\[Epsilon],regime,Mpts];
MapThread[(#1 CoherentSG[TotN,#2[[1]],#2[[2]],x,y])&,Transpose[coherentList]]//Total
]


End[];


(* ::Section:: *)
(*Package closure*)


EndPackage[];
