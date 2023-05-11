# agda-base
This is an *experimental* base library which is supposed to contain basic things, like basic datatypes and reflection code.
Equality (in the sense of typal/propositional equality) is out of scope (with the possible exception of things like 'primQNameEquality' or for example the inductively defined equality on the naturals). 

# contributions, comments and suggestions
... are very welcome.

# why?
The idea is to have a common denominator for all the different libraries (e.g. stdlib, cubical, 1lab, ...) and start to work against the tragedy, 
that so much gets implemented again and again, by making the code build on top of basic definitions interchangeable.

# plan
- [ ] copy enough from stdlib, to make basic [reflection code](https://github.com/omelkonian/stdlib-meta) run
- [ ] see how painful it is to make another library (cubical) run with this  
