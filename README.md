An experiment at enabling datatype-generic programming in Agda.
It's a happy blend of the work below.

Note: This implementation relies on the soon-to-be-released 2.6.2 version of Agda.
To play around with this code, you need to compile Agda from source.

Related work:
- McBride and Dagand's work on Universe descriptions.
- Yorick Sijsling's [master thesis](https://github.com/yoricksijsling/ornaments-thesis)
  about generic programming and ornaments.
- Effectfully's [`Generic` library](https://github.com/effectfully/generic)
- Larry Diehl's [`generic-elim` library](https://github.com/larrytheliquid/generic-elim)

Reading List:
- [Descriptions, Computational vs Propositional](http://effectfully.blogspot.com/2016/04/descriptions.html)
- [Deriving Eliminators of Described Datatypes](http://effectfully.blogspot.com/2016/06/deriving-eliminators-of-described-data.html)
