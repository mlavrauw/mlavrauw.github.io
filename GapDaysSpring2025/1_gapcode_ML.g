# Minicourse 3 by Michel Lavrauw
#
# 1. Projective spaces over finite fields in GAP (FinInG package)
#
# 2. Coding theory in GAP (guava package)
#
# 3. Incidence geometries and substructure (FinInG package)
#
#



# Lecture 1: Projective spaces over finite fields in GAP (FinInG package)

# A gentle introduction to FinInG
# webpage: <https://gap-packages.github.io/FinInG/>

# Load the FinInG package

LoadPackage("fining");
LogTo("lecture1_output.g");

# Projective spaces, affine spaces, points, lines, subspaces
#
# Notation PG(n,q), AG(n,q),
# n is the dimension (projective dimension),
# q is a prime power, the order of the basefield
pg:=PG(2,2);
BaseField(pg);
Points(pg);
List(Points(pg),x->Coordinates(x));
Display(last);
Lines(pg);
Size(last);
line:=Random(Lines(pg));
ProjectiveDimension(line);

UnderlyingObject(line);
Display(last);
UnderlyingObject(Random(Points(pg)));
Display(last);

ag:=AG(8,5);
Random(Planes(ag));
Display(last);

pg:=PG(9,7);
Random(Solids(pg));
Random(ElementsOfIncidenceStructure(pg,1));
Dimension(last);
Random(ElementsOfIncidenceStructure(pg,2));
Dimension(last);

Random(ElementsOfIncidenceStructure(pg,3));
Random(ElementsOfIncidenceStructure(pg,4));
Random(ElementsOfIncidenceStructure(pg,5));
Random(ElementsOfIncidenceStructure(pg,7));
Random(ElementsOfIncidenceStructure(pg,9));
Random(Hyperplanes(pg));

vecs:=List([1..6],i->Random(GF(7)^10));
VectorSpaceToElement(pg,vecs);


# Incidence, intersection, and span, flags
x:=Random(Points(pg));
plane:=Random(Planes(pg));
x in plane;

hyp:=Random(Hyperplanes(pg));
DualCoordinatesOfHyperplane(hyp);

y:=Random(Points(pg));
Span(x,y);
Meet(last,hyp);

linesony:=Lines(y);
Size(linesony);
hyp:=Span(y,First(ElementsOfIncidenceStructure(pg,8),sub->not y in sub));

sol:=First(Solids(hyp),s->y in s);

flag:=FlagOfIncidenceStructure(pg,[y,sol,hyp]);

shad:=ShadowOfElement(pg,sol,5);
ForAll(shad,sub->sol in sub);
5space:=Random(shad);

flag:=FlagOfIncidenceStructure(pg,[y,sol,5space,hyp]);
quit;
5space in hyp;
5space:=First(shad,s->s in hyp);
flag:=FlagOfIncidenceStructure(pg,[y,sol,5space,hyp]);

NamesOfComponents(flag);
flag!.types;
flag!.els;


# StandardDualityOfProjectiveSpace
sd:=StandardDualityOfProjectiveSpace(pg);

y^sd;
hyp^sd;
sol^sd;
y in hyp;
hyp^sd in y^sd;



# StandardFrame
frame:=StandardFrame(pg);
Display(List(last,x->Coordinates(x)));


# Projective groups
pg:=PG(3,8);
CollineationGroup(pg);
ProjectivityGroup(pg);
Size(last);
PGL(4,8);
SpecialProjectivityGroup(pg);
PSL(4,8);
Random(PSL(4,8));
Random(SpecialProjectivityGroup(pg));
Display(last);

# Frames and
frame:=StandardFrame(pg);
P1:=frame[1];
G:=ProjectivityGroup(pg);
GP1:=FiningStabiliser(G,P1);
P2:=frame[2];
FiningOrbit(GP1,P2);
GP1P2:=FiningStabiliser(GP1,P2);
P3:=frame[3];
FiningOrbit(GP1P2,P3);
FiningOrbits(GP1P2,Points(pg));
L12:=Span(P1,P2);
GL12:=FiningStabiliser(G,L12);
FiningOrbit(GL12,Span(P2,P3));
FiningOrbits(GL12,Lines(pg));

g:=Random(G);
frame2:=List(frame,x->x^g);
ProjectivityByImageOfStandardFrameNC(pg,frame2);
g=last;




hyp:=HyperplaneByDualCoordinates(pg,[0,0,0,1]*Z(8));
DualCoordinatesOfHyperplane(hyp);
p:=VectorSpaceToElement(pg,[1,1,1,1]*Z(8));
p in hyp;
G:=ProjectiveHomologyGroup(hyp,p);
Size(FiningOrbits(G,Points(pg)));



p:=VectorSpaceToElement(pg,[1,1,1,0]*Z(8));
p in hyp;
G:=ProjectiveElationGroup(hyp,p);
P1:=First(Points(pg),x->not x in hyp);
P2:=VectorSpaceToElement(pg,[0,0,0,1]*Z(8));
g:=ElationOfProjectiveSpace(hyp,P1,P2);
P1^g=P2;
ForAll(Points(hyp),x->x^g=x);



# Subgeometries, Field Reduction


subgeom:=SubgeometryOfProjectiveSpaceByFrame(pg,frame,GF(2));

pg1:=PG(2,8);
em:=NaturalEmbeddingByFieldReduction(pg1,GF(2));
pg2:=PG(8,2);
ProjectiveSpace(8, 2);

U:=RandomSubspace(pg2,3);
LU:=Filtered(Points(pg1),x->ProjectiveDimension(Meet(x^em,U))>-1);
ForAll(Lines(pg1),l->ForAny(Points(l),x->x in LU)); # We constructed a linear blocking set


phi:=Intertwiner(em);
g:=Random(ProjectivityGroup(pg1));
g^phi;
Display(g);
Display(g^phi);


frame:=StandardFrame(pg1);
lines:=List(Combinations(frame,2),ij->Span(ij));
P:=First(Points(pg1),x->not ForAny(lines,l->x in l));
vm:=VeroneseMap(pg1);
fivepoints:=Union(frame,[P]);
hyp:=Span(List(fivepoints,x->x^vm));
v:=DualCoordinatesOfHyperplane(hyp);
R:=PolynomialRing(GF(8),3);
monlist:=[R.1^2,R.1*R.2,R.1*R.3,R.2^2,R.2*R.3,R.3^2];
f:=Sum([1..6],i->v[i]*monlist[i]);
conic:=QuadraticVariety(pg1,f);
ForAll(fivepoints,x->x in conic);
ps:=PolarSpace(conic);
N:=NucleusOfParabolicQuadric(ps);
List(Lines(N),l->Number(Points(l),x->x in conic));



hv:=HermitianVariety(2,9);

sv:=SegreVariety([PG(1,2),PG(2,2)]);
svpts:=Points(sv);
G:=ProjectivityGroup(PG(5,2));

K:=FiningSetwiseStabiliser(G,AsSet(svpts));
FiningOrbits(K,Points(PG(5,2)));

sv:=SegreVariety([PG(1,3),PG(2,3)]);
svpts:=Points(sv);
Size(svpts);
G:=ProjectivityGroup(PG(5,3));
G:=FiningSetwiseStabiliser(G,AsSet(svpts));
FiningOrbits(G,Points(PG(5,3)));
ptorbs:=FiningOrbits(G,Points(PG(5,3)));
lineorbs:=FiningOrbits(G,Lines(PG(5,3)));


R:=PolynomialRing(GF(7),4);
f:=R.1*R.2-R.3*R.4;
pg:=PG(3,7);
qv:=QuadraticVariety(pg,f);
qf:=QuadraticForm(qv);
TypeOfForm(qf);


R:=PolynomialRing(GF(11),3);
f:=R.1*R.2-R.3^2;
pg:=PG(2,11);
qv:=QuadraticVariety(pg,f);
Size(Points(qv));
qf:=QuadraticForm(qv);
TypeOfForm(qf);
x:=Random(Points(qv));
Display(qf);
IsDegenerateForm(qf);
TypeOfForm(qf);
f:=R.1*R.2;
qv:=QuadraticVariety(pg,f);
qf:=QuadraticForm(qv);
TypeOfForm(qf);

















