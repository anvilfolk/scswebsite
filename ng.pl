/* 
  15/05/2013
  Implemented for "On Failure-Driven Constraint-Based Parsing through CHRG",
  Veronica Dahl, Sinan Eğilmez, João Martins and J. Emilio Miralles
  
  Based on previous code from Veronica Dahl and J. Emilio Miralles.
*/

:- compile('chrg').		

:- chrg_symbols word/3, g/1, falsify/1, wait/1, remove_falsify/1, iCat/3.

:- chr_constraint checkExistentialConstraints/0, unsat/1, tpl/1, parseOrder/1,
   failed/1, revert/0, revertFrom/1, revertTo/1, evil/1, relaxable/1, grow/0, clean/0.


% LEXICON: word(Category,Traits,Word) 

  [le] ::> word(det,[sing,masc],le).
  [les] ::> word(det,[plur,masc],le).
  [un] ::> word(det,[sing,masc],un).
  [une] ::> word(det,[sing,fem],un).
  [tres] ::> word(adv,[sing,masc],tres).
  
  %nouns
  [livre] ::> word(n,[sing,masc],livre).
  [livres] ::> word(n,[plur,masc],livre).

  [pomme] ::> word(n,[sing,fem],pomme).

  %adjectives
  [jaune] ::> word(adj,[sing,masc],jaune).
  [bleu] ::> word(adj,[sing,masc],bleu).

  %conjunction
  [et] ::> word(con,[na,na], et).

  %aux verb
  [a] ::> word(v,[sing, na], a).
  [mange] ::> word(v,[sing, na], mange).

  %proper name
  [amelie] ::> word(pn,[sing, feme], amelie).
  [jean] ::> word(pn,[sing, masc], jean).


% CREATE INSTANTIATED CATEGORIES FROM WORDS

word(Comp, Attr, Word) <:> Tree =.. [Comp,Word] | iCat(Comp, Attr, Tree).

% falsify LISTS
% falsifys simply adds more unsatisfied constraints to the list.

    %First check if property is already in the list, if so signal remove falsify without adding to list.
    % remove the falsify marker
    %if it was not in the list, add to list
  falsify(N0, N1, Prop), unsat(List) ==> member(g(N0, N1, Prop), List) | remove_falsify(N0, N1, Prop).
  falsify(N0, N1, Prop), remove_falsify(N0, N1, Prop) <=> true.
  falsify(N0, N1, Prop), unsat(List) <=> unsat([g(N0, N1, Prop) | List]). 

 % RUN SINGLE EXAMPLE

doParse(S) :- unsat([]), evil([]), init_grammar, parse(S), grow,clean.

% GRAMMAR
%
%
% INIT GRAMMAR

init_grammar :- tpl(constituency(sentence, [np, vp])),
                tpl(constituency(np, [n, pn, det, adj])),
                tpl(constituency(vp, [v, np])),
                tpl(obligatority(sentence,vp)),
                tpl(obligatority(sentence,np)),
                tpl(obligatority(vp,v)),
                tpl(precedence(sentence,np,vb)),
                tpl(precedence(np,det,n)),
                tpl(precedence(vp,v,np)),
                tpl(requirement(np, n, det)),
                tpl(requirement(sentence, np, vp)),
                %tpl(obligatority(vp, np)), % enable if verbs must have complements
                tpl(unicity(sentence,vp)),
                tpl(unicity(sentence,np)),
                tpl(unicity(vp,v)),
                tpl(unicity(vp,np)),
                tpl(unicity(np,det)), % extras for tests
                tpl(exclusion(np, det, pn)),
                tpl(dependence(np, det, n)),
                % This first relaxable allows VPs to expand into subjects, and sentences to be created therefrom
                %relaxable([unicity(vp,np),precedence(np,det,n),precedence(vp,v,np),obligatority(sentence,np)]),
                % This one allows VPs to grow into subjects, but not for sentences to be created
                %relaxable([unicity(vp,np),precedence(np,det,n),precedence(vp,v,np)]),
                % This one allows NPs to have determiners after the noun.
                %relaxable([precedence(np,det,n)]),
                % This one does proper parsing :)
                relaxable([]),
                %relaxable([exclusion(np,det,pn)]),
                parseOrder([np,vp,sentence]).

% CATEGORIES, KERNELS, ETC

category(sentence).
category(np).
category(vp).

head(n, np).
head(pn, np).
head(v, vp).
head(vp, sentence).

% TREE RULES
%
% Given two tree-like structures and the to-expand category, create a new tree.

buildTree(Cat,C1,C2,T) :- C1 = iCat(_, _, Cat,  _, T1),
                          C2 = iCat(_, _, Comp, _, _), !,
                          Cat \= Comp, T1=..[Cat|L1],
                          append(L1,[C2],L), T=..[Cat|L].

buildTree(Cat,C1,C2,T) :- C1 = iCat(_, _, Comp, _, _),
                          C2 = iCat(_, _, Cat , _, T2),
                          Cat \= Comp, T2=..[Cat|L2],
                          append([C1],L2,L), T=..[Cat|L].

% GRAMMAR RULES
%

% PRECEDENCE (universal property)
% prec(C,C1,C2) - any C1 within C must precede any C2 within that same C.
 
% Precedence is falsified whenever two categories C2, C1 are found in that order within the bounds of C.	
  iCat(C2,Attr2,Tree2):(N1,N2), ... ,         % Found C2
  iCat(C1,Attr1,Tree1):(N3,N4),               % Then a C1 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                   % And there's a Cat
  {tpl(precedence(Cat,C1,C2))}                % In Cats, C1's must come C2's
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],     % C1 and C2 within Cat
      member(iCat(N1,N2,C2,Attr2,Tree2), T),  % Both are direct descendents of Cat
      member(iCat(N3,N4,C1,Attr1,Tree1), T)
  | falsify(precedence(Cat,C1,C2)):(N1,N4),   % Precedence falsified!
    {failed(g(N1,N4,precedence(Cat,C1,C2)))}. % Failure of tentative category

  
% UNICITY (universal property)
% unicity(Cat,C) - only one C is allowed in a Cat

% Unicity fails whenever you can find two distinct Cs within the bounds of Cat.
  iCat(C,Attr1,Tree1):(N1,N2), ... ,        % Found C
  iCat(C,Attr2,Tree2):(N3,N4),              % Then another C sometime later
  {iCat(N5,N6,Cat,_,Tree)},                 % And there's a Cat
  {tpl(unicity(Cat,C))}                     % Unicity
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],   % Cs within Cat
      member(iCat(N1,N2,C,Attr1,Tree1), T), % Both are direct descendents of Cat
      member(iCat(N3,N4,C,Attr2,Tree2), T)
  | falsify(unicity(Cat,C)):(N1,N4),        % Unicity falsified!
    {failed(g(N1, N4, unicity(Cat,C)))}.    % Failure of tentative category
  
% EXCLUSION (universal property)
% exclusion(Cat,C1,C2) - C1 and C2 must not both occur in a Cat

% If we can find both a C1 and C2 (in either ordering) within a Cat, exclusion fails
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,          % Found C1
  iCat(C2,Attr2,Tree2):(N3,N4),                % Then a C2 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                    % And there's a Cat
  {tpl(exclusion(Cat,C1,C2))}                  % Exclusion
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],      % C1 and C2 within Cat
      member(iCat(N1,N2,C1,Attr1,Tree1), T),   % Both are direct descendents of Cat
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(exclusion(Cat,C1,C2)):(N1,N4),     % Exclusion falsified!
    {failed(g(N1, N4, exclusion(Cat,C1,C2)))}. % Failure of tentative category
  
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,        % Symmetry, C2 and C1
  iCat(C2,Attr2,Tree2):(N3,N4),
  {iCat(N5,N6,Cat,_,Tree)},
  {tpl(exclusion(Cat,C2,C1))}
  ::> N5 =< N1, N4 =< N6, Tree=..[Cat|T],
      member(iCat(N1,N2,C1,Attr1,Tree1), T),
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(exclusion(Cat,C2,C1)):(N1,N4),
    {failed(g(N1, N4, exclusion(Cat,C2,C1)))}.


% DEPENDENCE (universal property)
% dependence(Cat,C1,C2) - the traits of C1 determine the traits of C2 inside a C

% If we can find C1 and C2 (in either ordering) whose two attributes are different, dependence fails
  iCat(C1,Attr1,Tree1):(N1,N2), ... ,           % Found C1
  iCat(C2,Attr2,Tree2):(N3,N4),                 % Then a C2 sometime later
  {iCat(N5,N6,Cat,_,Tree)},                     % And there's a Cat
  {tpl(dependence(Cat,C1,C2))}                  % Dependence & constraint phase
  ::> Attr1 \= Attr2,                           % Attributes differ
      N5 =< N1, N4 =< N6, Tree=..[Cat|T],       % C1 and C2 within Cat
      member(iCat(N1,N2,C1,Attr1,Tree1), T),    % Both are direct descendents of Cat
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(dependence(Cat,C1,C2)):(N5,N6),     % Dependence falsified!
    {failed(g(N5, N6, dependence(Cat,C1,C2)))}. % Failure of tentative category

  iCat(C1,Attr1,Tree1):(N1,N2), ... ,           % Symmetric
  iCat(C2,Attr2,Tree2):(N3,N4),
  {iCat(N5,N6,Cat,_,Tree)},
  {tpl(dependence(Cat,C2,C1))}
  ::> Attr1 \= Attr2,
      N5 =< N1, N4 =< N6, Tree=..[Cat|T],
      member(iCat(N1,N2,C1,Attr1,Tree1), T),
      member(iCat(N3,N4,C2,Attr2,Tree2), T)
  | falsify(dependence(Cat,C2,C1)):(N5,N6),
    {failed(g(N5, N6, dependence(Cat,C2,C1)))}.


% IF THINGS FAILED, REVERT!

% If a non-relaxable property failed, it's time to revert. If all properties are relaxable, revert won't fire!
failed(g(_, _, Prop)), relaxable(R) ==> not(member(Prop, R)) | revert.
revert, revert <=> revert. % Only one revert.

% Since we are reverting, remove all unsatisfied properties until no more failed(P) apply.
revert \ unsat(L), failed(P) <=> delete(L, P, L2), nl,write('FAILED ':P:(L):(L2)), nl | unsat(L2).

% Revert for universal properties - remove the revertFrom/To predicates, the From, and add the To.
% Also add the failed predicate to the evil list!
 evil(E), revert,                              % Need to revert
 revertFrom(iCat(N1,N2,Cat1, Attr1, Tree1)),   % from this
 revertTo(iCat(N3,N4,Cat2, Attr2, Tree2)),     % To this
 iCat(N1,N2,Cat1, Attr1, Tree1)                % Replace predicate to revert from
 <=> evil([iCat(N1,N2,Cat1, Attr1, Tree1)|E]), % And revertFrom is evil!
     iCat(N3,N4,Cat2, Attr2, Tree2).           % with the one to revert to
     
  
% Revert for existential properties. Need to remove the From, and add the head of the category
% to the evil list - not the entire predicate!
 evil(E), revert,                            % Need to revert
 revertFrom(iCat(N1,N2,Cat, Attr1, Tree1)),  % from this
 revertTo(none),                             % to nothing!
 iCat(N1,N2,Cat, Attr1, Tree1)               % Remove this predicate
 <=> Tree1=..[Cat|T], head(Comp, Cat),       % Look at the category's children
     member(iCat(N3,N4,Comp,Attr2,Tree2), T) % Find the head!
 | evil([iCat(N3,N4,Cat,Attr2,Tree2)|E]).    % Mark growing from the head Comp to head Cat as impossible

% In case there was no revert, simply remove the revertFroms, and the failed (which were relaxed for sure).
%revertFrom(F), revertTo(T) <=> nl, write('Revert from '-F-' to '-T), nl | true.
revertFrom(_), revertTo(_) <=> true.
failed(P) <=> write('go away '-P)| true.

% EXPANDING CATEGORIES - WITH CONSTRAINTS

   !iCat(Comp, Attr1, Tree1):(N1,N2), iCat(Cat, Attr2, Tree2):(N2,N3), % Comp next to Cat, subcategories stay, to-expand category disappears
   !{tpl(constituency(Cat, L))},!{evil(EL)},         % L is the set of constituents of Cat
   !{parseOrder([Cat|_])}                            % Ensure things are parsed in order
  <:> not(member(iCat(N1,N3,Cat, Attr2, Tree), EL)), % A constituent that is not a super-horrible thing.
      member(Comp, L),                               % Comp is a basic word constituent of Cat
      buildTree(Cat, iCat(N1,N2,Comp, Attr1, Tree1),
                     iCat(N2,N3,Cat , Attr2, Tree2),
                     Tree)                           % Build the tree for the expanded Cat
  | iCat(Cat, Attr2, Tree):(N1,N3),                  % Create expanded Cat, replacing the smaller, previous one
    {revertFrom(iCat(N1,N3,Cat, Attr2, Tree))},
    {revertTo(iCat(N2,N3,Cat, Attr2, Tree2))}.

   iCat(Cat, Attr1, Tree1):(N1,N2), !iCat(Comp, Attr2, Tree2):(N2,N3), % Symmetric rule
   !{tpl(constituency(Cat, L))}, !{evil(EL)},
   !{parseOrder([Cat|_])}
  <:> not(member(iCat(N1,N3,Cat, Attr1, Tree), EL)),
      member(Comp, L),
      buildTree(Cat, iCat(N1,N2,Cat , Attr1, Tree1),
                     iCat(N2,N3,Comp, Attr2, Tree2), Tree)
  | iCat(Cat, Attr1, Tree):(N1,N3),
    {revertFrom(iCat(N1,N3,Cat, Attr1, Tree))},
    {revertTo(iCat(N1,N2,Cat, Attr1, Tree1))}.



% OBLIGATORITY (existential property)
% obligatority(Cat, C) - all categories of type Cat must have a C included.

% After all possible expansions, obligatority is checked. If there are no C categories as
% direct descendents, then the property is violated.
   iCat(Cat, Attr, Tree):(N1,N2),              % Found Cat
   {tpl(obligatority(Cat, C))}                 % Cat should have C
  ::> Tree=..[Cat|T],                          % Get children
      not(member(iCat(_,_,C,_,_), T))          % There isn't a child C
  | falsify(obligatority(Cat, C)),             % The property is violated!
    {failed(g(N1, N2, obligatority(Cat, C)))}, % Local falsification
    {revertFrom(iCat(N1,N2,Cat, Attr, Tree))}, % Going to remove the falsifying category
    {revertTo(none)}.                          % And not replacing it with anything



% REQUIREMENT (existential property)
% requirement(C,C1,C2) - if there is a C1 in C, then there must also be a C2
 
% If one can find a category of type C1 within a category of type C, then one must wait for a
% category of type C2 within the boundaries of C. Satisfaction is the same as above.

   iCat(Cat, Attr, Tree):(N1,N2),                % Found Cat
   {tpl(requirement(Cat,C1,C2))}                 % If there's a C1, there should be a C2
  ::> Tree=..[Cat|T],                            % Get children
      member(iCat(_,_,C1,_,_), T),               % There is a C1
      not(member(iCat(_,_,C2,_,_), T))           % But not a C2 :(
  | falsify(requirement(Cat,C1,C2)):(N1,N2),     % The property is violated!
    {failed(g(N1, N2, requirement(Cat,C1,C2)))}, % Local falsification
    {revertFrom(iCat(N1,N2, Cat, Attr, Tree))},  % Going to remove the falsifying category
    {revertTo(none)}.                            % And not replacing it with anything


% KERNELS ARE CATEGORIES AT THE CATEGORY LEVEL
iCat(Comp,Attr,Tree):(N1,N2), {parseOrder([Cat|_])} ::> head(Comp, Cat), NewTree=..[Cat,iCat(N1,N2,Comp,Attr,Tree)] | iCat(Cat, Attr, NewTree).

grow \ parseOrder([_|L]) <=> parseOrder(L).



% cleanup
clean \ tpl(_)        <=> true.
clean \ grow          <=> true.
clean \ token(_,_,_)  <=> true.
clean \ parseOrder(_) <=> true.
clean , all(_,_)      <=> true.

end_of_CHRG_source.

% TODO LIST
% doParse([le, pomme]). % fails dependence(no, det, m)


% doParse([jean,mange, une, pomme]).

% doParse([jean, mange, pomme, une]). % fails precedence(np, det, n)
% doParse([jean, mange, pomme]). % fails requirement(np, n, det)