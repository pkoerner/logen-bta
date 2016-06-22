


taist(X) :- foo(X),
            foo(a).

bar(a).

foo(X) :- bar(B).
foo(b).
foo(c).
