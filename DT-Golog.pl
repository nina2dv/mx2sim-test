 /*                            APPENDIX  C
                        Section C.1  An Interpreter
*/
/********************************************************************
   An Offline Decision Theoretic Golog Interpreter (non-temporal version)    
                        October, 1999.              

            Do not distribute without permission.
            Include this notice in any copy made.

Permission to use, copy, and modify this software and its documentation 
for non-commercial research purpose is hereby granted without fee,
provided that this permission notice appears in all copies. This
software cannot be used for commercial purposes without written permission.
This software is provided "as is" without express or implied warranty
(including all implied warranties of merchantability and fitness).
No liability is implied for any damages resulting from 
or in connection with the use or performance of this software.

The following paper provides the technical background:
@inproceedings{AAAI,
   author = {Boutilier, C. and  Reiter, R. and
             Soutchanski, M. and Thrun, S.},
  title={Decision-Theoretic, High-level Robot Programming in
           the Situation Calculus},
  booktitle = {Proc. of the 17th National Conference on
    Artificial Intelligence (AAAI'00)},
  address={Austin, Texas},
  publisher = {Available at:  http://www.cs.toronto.edu/~cogrobo },
  year= 2000
}

E-mail questions about the interpreter to Mikhail Soutchanski:
                     mes [at] cs [dot] toronto [dot] edu   

NOTICE: this software works on Unix/Linux machines with Eclipse Prolog that is
        available from IC-PARK (Imperial College, London, UK). It is easy to
        modify this interpreter to work with any other version of Prolog.
        
**********************************************************************/
  
:- dynamic(proc/2).            /* Compiler directives. Be sure   */
:- set_flag(all_dynamic, on).     /* that you load this file first! */
:- set_flag(print_depth,500).
/* :- pragma(debug).  */
 
:- op(900, fy, [not]).
(not X) := (\+ X).
cputime(5).

:- op(800, xfy, [&]).   /* Conjunction */
:- op(850, xfy, [v]).   /* Disjunction */
:- op(870, xfy, [=>]).  /* Implication */
:- op(880,xfy, [<=>]).  /* Equivalence */
:- op(950, xfy, [:]).   /* Action sequence */
:- op(960, xfy, [#]).   /* Nondeterministic action choice */

/* The predicate bp() is the top level call. Add an end-of-program 
   marker "nil" to the tail of program expression E , then compute 
   the best policy that succeeds with probability Prob. The horizon
   H must be a non-negative integer number.
*/

 
bp(E,H,Pol,Util,Prob,File) :- integer(H), H >= 0, 
      cputime(StartT), 
      bestDo(E : nil,s0,H,Pol,Val,Prob),
      cputime(EndT), Elapsed is EndT - StartT,
      Util is float(Val),
      open( File, append, Stream),
      date(Date),
      printf(Stream, "\n\n    This report is started at time %w\n", [Date]),
      ( proc(E,Body) -> 
        printf(Stream, "The Golog program is\n proc(%w,\n  %w)\n",[E,Body]) ;
        printf(Stream, "The Golog program is\n %w\n",[E])
       ),
      printf("\nThe computation took %w seconds",[Elapsed]),
      printf(Stream, "\nTime elapsed is %w seconds\n", [Elapsed]),
       printf(Stream, "The optimal policy is \n %w \n", [Pol]),
       printf(Stream, "The value of the optimal policy is %w\n",[Util]),
    printf(Stream, "The probability of successful termination is %w\n",[Prob]),
       close(Stream).
  

/*  bestDo(E,S,H,Pol,V,Prob) 
  Given a Golog program E and situation S find a policy Pol of the highest
  expected utility Val. The optimal policy covers a set of alternative histories 
  with the total probability Prob. H is a given finite horizon.
*/

bestDo((E1 : E2) : E,S,H,Pol,V,Prob) :-   H >= 0, 
           bestDo(E1 : (E2 : E),S,H,Pol,V,Prob).

bestDo(?(C) : E,S,H,Pol,V,Prob) :-   H >= 0, 
          holds(C,S) ->  bestDo(E,S,H,Pol,V,Prob) ;
                 ( (Prob is 0.0) , Pol = stop, reward(V,S) ).

bestDo((E1 # E2) : E,S,H,Pol,V,Prob) :-  H >= 0, 
     bestDo(E1 : E,S,H,Pol1,V1,Prob1), 
     bestDo(E2 : E,S,H,Pol2,V2,Prob2), 
     ( lesseq(V1,Prob1,V2,Prob2), Pol=Pol2, Prob=Prob2, V=V2 ; 
       greatereq(V1,Prob1,V2,Prob2), Pol=Pol1, Prob=Prob1, V=V1).

bestDo(if(C,E1,E2) : E,S,H,Pol,V,Prob) :-   H >= 0, 
               holds(C,S) -> bestDo(E1 : E,S,H,Pol,V,Prob) ;
                             bestDo(E2 : E,S,H,Pol,V,Prob).

bestDo(while(C,E1) : E,S,H,Pol,V,Prob) :-   H >= 0, 
          holds(-C,S) -> bestDo(E,S,H,Pol,V,Prob) ;
                         bestDo(E1 : while(C,E1) : E,S,H,Pol,V,Prob).

bestDo(ProcName : E,S,H,Pol,V,Prob) :-   H >= 0, 
              proc(ProcName,Body), 
              bestDo(Body : E,S,H,Pol,V,Prob).

/* Non-decision theoretic version of pi: pick a fresh value of X
   and for this value do the complex action E1 followed by E.
*/
bestDo(pi(X,E1) : E,S,H,Pol,V,Prob) :-   H >= 0, 
            sub(X,_,E1,E1_X), bestDo(E1_X : E,S,H,Pol,V,Prob).

/*                   
  Discrete version of pi. pickBest(x,f,e) means: choose the best value 
   of x from the finite non-empty range of values f, and for this x, 
   do the complex action expression e.
*/
bestDo(pickBest(X,F,E) : EF,S,H,Pol,V,Prob) :-  H >= 0,
        range(F,R), 
        ( R=[D],    sub(X,D,E,E_D),
                      bestDo(E_D : EF,S,H,Pol,V,Prob)           ;
          R=[D1,D2], sub(X,D1,E,E_D1), sub(X,D2,E,E_D2), 
                      bestDo((E_D1 # E_D2) : EF,S,H,Pol,V,Prob)  ;
          R=[D1,D2 | Tail], Tail = [D3 | Rest], 
                     sub(X,D1,E,E_D1), sub(X,D2,E,E_D2), 
          bestDo((E_D1 # E_D2 # pickBest(X,Tail,E)) : EF,S,H,Pol,V,Prob) 
         ).

bestDo(A : E,S,H,Pol,V,Prob) :-   H > 0, 
      agentAction(A), deterministic(A,S),
      ( not poss(A,S), Pol = stop, (Prob is 0.0) , reward(V,S) ;
        poss(A,S), Hor is H - 1, 
        bestDo(E,do(A,S),Hor,RestPol,VF,Prob),
        reward(R,S), 
        V is R + VF, 
        ( RestPol = nil,     Pol = A ; 
          not RestPol=nil,   Pol = (A : RestPol) 
         )
       ).

bestDo(A : E,S,H,Pol,V,Prob) :-   H > 0, 
       agentAction(A), nondetActions(A,S,NatOutcomesList),
       Hor is H -1,
       bestDoAux(NatOutcomesList,E,S,Hor,RestPol,VF,Prob),
       reward(R,S),  
       V is R + VF, 
       Pol=(A : senseEffect(A) : (RestPol)).

bestDoAux([N1],E,S,H,Pol,V,Prob) :-   H >= 0, senseCondition(N1,Phi1),
     ( not poss(N1,S), ( Pol = (?(Phi1) : stop ), (Prob is 0.0) , V is 0 ) ;
       poss(N1,S), 
       prob(N1,Pr1,S),
       bestDo(E,do(N1,S),H,Pol1,V1,Prob1), !,
       Pol = ( ?(Phi1) : Pol1 ),
       V is Pr1*V1, 
       Prob is Pr1*Prob1 ).

bestDoAux([N1 | OtherOutcomes],E,S,H,Pol,V,Prob) :-  H >= 0, 
     OtherOutcomes = [Head | Tail],  % there is at least one other outcome
     ( not poss(N1,S) -> bestDoAux(OtherOutcomes,E,S,H,Pol,V,Prob) ;
       poss(N1,S), 
       bestDoAux(OtherOutcomes,E,S,H,PolT,VT,ProbT),
       senseCondition(N1,Phi1),
       prob(N1,Pr1,S),
       bestDo(E,do(N1,S),H,Pol1,V1,Prob1), !,
       Pol = if(Phi1,  % then
                             Pol1,  % else
                                           PolT),
       V is VT + Pr1*V1, 
       Prob is ProbT + Pr1*Prob1 ).


bestDo(nil,S,H,Pol,V,Prob) :- 
                Pol=nil, reward(V,S), (Prob is 1.0) .

bestDo(nil : E,S,H,Pol,V,Prob) :- H > 0, bestDo(E,S,H,Pol,V,Prob).

bestDo(stop : E,S,H,Pol,V,Prob) :-  
                Pol=stop, reward(V,S), (Prob is 0.0) .   

bestDo(E,S,H,Pol,V,Prob) :- H =:= 0, 
	/*  E=(A : Tail), agentAction(A),  */ 
              Pol=nil, reward(V,S), (Prob is 1.0) .


  /* ---- Some useful predicates mentioned in the interpreter ----- */

lesseq(V1,Prob1,V2,Prob2) :-  Pr1 is float(Prob1), (Pr1 = 0.0) ,
         Pr2 is float(Prob2), 
         ( (Pr2 \= 0.0) ; 
           (Pr2 = 0.0) ,  V1 =< V2
          ).

lesseq(V1,Prob1,V2,Prob2) :-  
            (Prob1 \= 0.0) , (Prob2 \= 0.0) , V1 =< V2.

greatereq(V1,Prob1,V2,Prob2) :-   (Prob1 \= 0.0) , (Prob2 = 0.0) .

greatereq(V1,Prob1,V2,Prob2) :-
            (Prob1 \= 0.0) , (Prob2 \= 0.0) , V2 =< V1.


deterministic(A,S) :- not nondetActions(A,S,OutcomesList).


range([D | Tail],[D | Tail]).     % Tail can be []

/* sub(Name,New,Term1,Term2): Term2 is Term1 with Name
   replaced by New. */
 
sub(X1,X2,T1,T2) :- var(T1), T2 = T1.
sub(X1,X2,T1,T2) :- not var(T1), T1 = X1, T2 = X2.
sub(X1,X2,T1,T2) :- not T1 = X1, T1 =..[F|L1], sub_list(X1,X2,L1,L2),
                    T2 =..[F|L2].
sub_list(X1,X2,[],[]).
sub_list(X1,X2,[T1|L1],[T2|L2]) :- sub(X1,X2,T1,T2),
                                   sub_list(X1,X2,L1,L2).

/* The holds predicate implements the revised Lloyd-Topor
   transformations on test conditions.  */
 
holds(P & Q,S) :- holds(P,S), holds(Q,S).
holds(P v Q,S) :- holds(P,S); holds(Q,S).
holds(P => Q,S) :- holds(-P v Q,S).
holds(P <=> Q,S) :- holds((P => Q) & (Q => P),S).
holds(-(-P),S) :- holds(P,S).
holds(-(P & Q),S) :- holds(-P v -Q,S).
holds(-(P v Q),S) :- holds(-P & -Q,S).
holds(-(P => Q),S) :- holds(-(-P v Q),S).
holds(-(P <=> Q),S) :- holds(-((P => Q) & (Q => P)),S).
holds(-all(V,P),S) :- holds(some(V,-P),S).
holds(-some(V,P),S) :- not holds(some(V,P),S).  /* Negation */
holds(-P,S) :- isAtom(P), not holds(P,S).     /* by failure */
holds(all(V,P),S) :- holds(-some(V,-P),S).
holds(some(V,P),S) :- sub(V,_,P,P1), holds(P1,S).
 
/* The following clause treats the holds predicate for all atoms,
   including Prolog system predicates. For this to work properly,
   the GOLOG programmer must provide, for all atoms taking a
   situation argument, a clause giving the result of restoring
   its suppressed situation argument, for example:
          restoreSitArg(ontable(X),S,ontable(X,S)).             */
 
holds(A,S) :- restoreSitArg(A,S,F), F ;
           not restoreSitArg(A,S,F), isAtom(A), A.
 
isAtom(A) :- not (A = -W ; A = (W1 & W2) ; A = (W1 => W2) ;
    A = (W1 <=> W2) ; A = (W1 v W2) ; A = some(X,W) ; A = all(X,W)).