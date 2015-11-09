%Lab 1 in Logic.
%Created by Arsalan Syed, 10th October 2015.
%This program takes a proof that uses natural deduction
%and determines whether or not the proof is correct. 

%Takes a file and verifies it. 
verify(InputFileName) :- see(InputFileName),
						 read(Prems), read(Goal), read(Proof),
						 seen,
						 valid_proof(Prems, Goal, Proof).

%Checks each line in the proof and if all of them are valid, returns true.
valid_proof(Prems,Goal,Proof) :- checkLastLine(Goal,Proof),checkProof(Proof,Prems,Proof). 
						 
%checks if last line in the proof is the same as the goal. 
checkLastLine(Goal,Proof) :- last(Proof,LastLine),find2ndOfList(LastLine,Goal). 

%iterate over each line in the proof and see if it is valid. 
checkProof([],_,_). 
checkProof([H|T],Prems,Proof) :- checkProofLine(H,Prems,Proof),checkProof(T,Prems,Proof).

%checks an individual line in the proof. Has individual cases for premises,
%assumption, a rule with no arity, assumption rules and all other rules.
checkProofLine([_,_,write(X)],_,_) :- !,false.
checkProofLine([LineNum,Term,premise],Prems,Proof) :- searchInList(Prems,Term),!,lineVerifPrint(LineNumNum). 
checkProofLine([[LineNum,_,assumption]|T],_,Proof) :- checkProof(T,_,Proof),lineVerifPrint(LineNum).

checkProofLine([LineNum,Term,lem],_,Proof) :- !,lem(Term),lineVerifPrint(LineNum).

checkProofLine([LineNum,Term,orel(X,Y,U,V,W)],_,Proof) :- !,checkArgs(LineNum,orel(X,Y,U,V,W)),orel(X,Y,U,V,W,Proof,Term),lineVerifPrint(LineNum).
checkProofLine([LineNum,Term,impint(X,Y)],_,Proof) :- !,checkArgs(LineNum,impint(X,Y)),checkLevelsAssumption(LineNum,impint(X,Y),Proof),impint(X,Y,Proof,Term),lineVerifPrint(LineNum).
checkProofLine([LineNum,Term,negint(X,Y)],_,Proof) :- !,checkArgs(LineNum,negint(X,Y)),checkLevelsAssumption(LineNum,negint(X,Y),Proof),negint(X,Y,Proof,Term),lineVerifPrint(LineNum).
checkProofLine([LineNum,Term,pbc(X,Y)],_,Proof) :- !,checkArgs(LineNum,pbc(X,Y)),checkLevelsAssumption(LineNum,pbc(X,Y),Proof),pbc(X,Y,Proof,Term),lineVerifPrint(LineNum).

checkProofLine([LineNum,Term,Func],_,Proof) :- !,checkArgs(LineNum,Func),checkLevels(LineNum,Func,Proof),call(Func,Proof,Term),lineVerifPrint(LineNum).

%Rules: X,Y,U,V,W are line numbers
andint(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,PredY),Term==and(PredX,PredY).
andel1(X,Proof,Term) :- findInProof(X,Proof,and(Term,_)). 
andel2(X,Proof,Term) :- findInProof(X,Proof,and(_,Term)). 

orint1(X,Proof,Term) :- findInProof(X,Proof,Pred),arg(1,Term,Pred).
orint2(X,Proof,Term) :- findInProof(X,Proof,Pred),arg(2,Term,Pred).

%eliminate or from or(A,B).
%X is line containing or(A,B).
%Y,U are start and finish of assump box for A.
%V,W are start and finish of assump box for B.
orel(X,Y,U,V,W,Proof,Term) :- findInProof(X,Proof,or(A,B)),findInProof(Y,Proof,A),findInProof(U,Proof,Term),findInProof(V,Proof,B),findInProof(W,Proof,Term).

negnegint(X,Proof,Term) :- findInProof(X,Proof,Pred),arg(1,Term,NegPred),arg(1,NegPred,Pred).
negnegel(X,Proof,Term) :- findInProof(X,Proof,neg(neg(Term))). %Pred=neg(neg(Term)).

impint(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,PredY),Term=imp(PredX,PredY).
impel(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,imp(PredX,Term)). %,PredY=imp(PredX,Term).

negel(X,Y,Proof,Term) :- number(X),number(Y),Term=cont,findInProof(X,Proof,PredX),findInProof(Y,Proof,PredY),!,neg(PredX)=PredY.
negint(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,cont),!,neg(PredX)=Term.
 
contel(X,Proof,Term) :- findInProof(X,Proof,cont). %as long as cont is specified, it doesnt matter what the Term is. 

copy(X,Proof,Term) :- findInProof(X,Proof,Term). 
mt(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,PredY),arg(1,PredX,P),arg(2,PredX,Q),neg(P)=Term,neg(Q)=PredY.     
lem(Term) :- arg(1,Term,P),arg(2,Term,Q),neg(P)=Q.
pbc(X,Y,Proof,Term) :- findInProof(X,Proof,PredX),findInProof(Y,Proof,cont),!,PredX=neg(Term).

%Failed Rules: These are called if the proof structure is wrong for assumptions and premises.
assumption(X,Y) :- false. 
premise(X,Y) :- false.

find1stOfList([A|T],A).
find2ndOfList([_,B|T],B).
find3rdOfList([_,_,C|T],C).

%Finds the Term in the proof at line N
findInProof(N,[NextLine|T],Term) :- find1stOfList(NextLine,N),find2ndOfList(NextLine,Term).
findInProof(N,[NextLine|T],Term) :- find1stOfList(NextLine,First),isList(First),findInProof(N,NextLine,Term).
findInProof(N,[NextLine|T],Term) :- findInProof(N,T,Term).

searchInList([H|T],H). 
searchInList([H|T],X) :- searchInList(T,X).

isList([_|_]).
isList([]).

lineVerifPrint(LineNum) :- LineNum=1,write("\n"),write("Line "),write(LineNum),write(" fullfilled"),write("\n").
lineVerifPrint(LineNum) :- write("Line "),write(LineNum),write(" fullfilled"),write("\n").

%Check if line we are calling from is greater than lined we are calling to. 
checkArgs(Num,Func) :- functor(Func,_,1),arg(1,Func,Arg1),number(Arg1),Num>Arg1.
checkArgs(Num,Func) :- functor(Func,_,2),arg(1,Func,Arg1),arg(2,Func,Arg2),number(Arg1),number(Arg2),isGre(Num,Arg1,Arg2).
checkArgs(Num,Func) :- functor(Func,_,5),arg(1,Func,Arg1),arg(2,Func,Arg2),arg(3,Func,Arg3),arg(4,Func,Arg4),arg(5,Func,Arg5),isGre(Num,Arg1,Arg2,Arg3,Arg4,Arg5).

isGre(A,B,C) :- A>B,A>C.
isGre(A,B,C,D,E,F) :- A>B,A>C,A>D,A>E,A>F.

%Finds the Level in the proof of line N
levelInProof([],N,Term,Level,ResLevel) :- write("Could not find line: "),write(N),false.
levelInProof(N,[NextLine|T],Level,ResLevel) :- find1stOfList(NextLine,N),ResLevel=Level.
levelInProof(N,[NextLine|T],Level,ResLevel) :- find1stOfList(NextLine,First),isList(First),NewLevel is Level+1,levelInProof(N,NextLine,NewLevel,ResLevel).
levelInProof(N,[NextLine|T],Level,ResLevel) :- levelInProof(N,T,Level,ResLevel).

%Check if the arguments have corret levels
checkLevels(LineNum,Func,Proof) :- arg(1,Func,Arg1),levelInProof(LineNum,Proof,0,LineLevel),levelInProof(Arg1,Proof,0,A1level),!,number(LineLevel),number(A1level),LineLevel>=A1level.
checkLevels(LineNum,Func,Proof) :- arg(1,Func,Arg1),arg(2,Func,Arg2),levelInProof(LineNum,Proof,0,LineLevel),levelInProof(Arg1,Proof,0,A1level),levelInProof(Arg2,Proof,0,A2level),!,number(LineLevel),number(A1level),number(A2level),LineLevel>=A1level,LineLevel>=A2level.

%Check if the arguments have corret levels (assumption based rules only)
checkLevelsAssumption(LineNum,Func,Proof) :- functor(Func,_,2),arg(1,Func,Arg1),arg(2,Func,Arg2),levelInProof(LineNum,Proof,0,LineLevel),levelInProof(Arg1,Proof,0,A1level),levelInProof(Arg2,Proof,0,A2level),!,number(LineLevel),number(A1level),number(A2level),A1level is LineLevel+1,A1Level=A2Level.
