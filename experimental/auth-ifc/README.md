This folder contains a few datalog rules to try to prototype a combination of 
IFC and authorization logic. The idea is to see how far we could get with an 
extremely minimal language that can be implemented purely by translation into 
convetional datalog.

This is written using [souffle](https://souffle-lang.github.io/install). If I 
recall correctly, installing on mac with brew worked as advertised.

The makefile runs the two tests.

File description:
    (Might be easiest to follow if you start by reading flowsToAxioms.dl)
    "flowsToAxioms.dl" -- a simplified set of internal axioms that cuts out the 
    detail of "says". It could be useful to read this before the following 
    file.
    "flowsToAxioms_test.dl" -- a simple test of the above
    "flowsToSaysAxioms.dl" -- a set of axioms that are either internal to the 
    extended language, are in a library, or are otherwise things that a 
    programmer would not generally look at
    "frontendMockup.dl" -- This is not valid datalog. This gives a draft at 
    what a minimal frontend could look like.
    "flowsToSaysAxioms_test.dl" -- This includes a mechanical translation from 
    frontendMockup into normal datalog. Includes another simple test.

A very short description of the translation is that propositions of the form
    "X says some_relation(n, m)" 
    gets translated into
    "some_relation(X, n, m)"

and there are a few built-in rules. Implementing the extended language has the 
advantage that the implementation would be quite simple, but I think we would 
give up the ability to write things like:

"X says (Y says P)"

where one principal makes a statement involving statements by other principals. 
This kind of statement could be useful if combined with a delegation from Y to 
X. However, it might be that we don't really need this feature to capture 
real-world policies. (Worth looking into!)
