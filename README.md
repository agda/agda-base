# status
At his points, this is just a happy heap of code mixed together from the stdlib, stdlib-meta, 1lab (on a branch).
The purpose so far, was to figure out how feasible it is to have a common base library.
It seems doable, but it is too much work to do right now (certainly for me alone).
Things that seem a lot of work:
+ It essentially means maintaining some (aparantly not so small) part of the stdlib here and cutting it out in a reasonable way.
+ There is some stuff on top of the stdlib about monads/effects/etc. I don't know how to make a reasonable choice here, that people would accept, since it is not really my area of expertise.
+ Picking the right way to deal with all the things coming up in reflection code, also seems to be above my current skills/knowledge.

So for know, I (Felix Cherubini) will just look into running 1lab tactics in the cubical library, since this is why I was thinking more seriously about agda-base anyway...

# agda-base
This is an *experimental* base library which is supposed to contain basic things, like basic datatypes and reflection code.
It should be reasonable, to factor out another dependency, the agda-primitives, since the 1lab does things differently here.
Equality (in the sense of typal/propositional equality) is out of scope (with the possible exception of things like 'primQNameEquality' or for example the inductively defined equality on the naturals). 

# contributions, comments and suggestions
... are very welcome.

# why?
The idea is to have a common denominator for all the different libraries (e.g. stdlib, cubical, 1lab, ...) and start to work against the tragedy, 
that so much gets implemented again and again, by making the code build on top of basic definitions interchangeable.
