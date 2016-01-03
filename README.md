Alpha
=====

Reference compiler for the Alpha programming language. Inspired by Andrew W. Appel's Modern Compiler Implementation in ML.

## What is Alpha? ##

* Alpha is an garbage collected, imperative-styled programming language with features known from object oriented and functional languages.
* Language constructs such as if/else, while, for and function calls work as expected.
* Functions are first-class, meaning that they can be parsed around just as regular variables
* Lambda functions capture their lexically enclosing variables. These two features allows a continuation-passing style approach as seen below.

```javascript
fun sum(int n, fun(int) -> int f) -> int {
    if(n == 0) {
        return f(0);
    }
    else {
        return sum(n-1, (int k) -> int {
            return f(k) + n;
        });
    }
}

fun identity(int n) -> int {
    return n;
}

fun main() -> int {
    int n = sum(10, identity);
    return n;
}
```

Or, using a more procedural style, by summing the values of an array:

```javascript
fun sum([int] a, int n) -> int {
    int total = 0;
    for(int i = 0; i < n; ++i) {
        total += a[i];
    }
    return total;
}

fun main() -> int {
    var a = int[10];
    for(int i = 0; i < 10; ++i) {
        a[i] = i+1;
    }
    return sum(a, 10);
}
```
* Floating point computation is achieved using the float datatype. The following example shows a simple approximation of pi using [Leibniz formula for pi](http://en.wikipedia.org/wiki/Leibniz_formula_for_%CF%80):

```javascript
fun calcPi(float n) -> float {
    float pi = 1.0;
    for (float i = 3.0; i <= n; i += 4.0) {
        pi -= 1.0 / i;
        pi += 1.0 / (i + 2.0);
    }
    return pi * 4.0;
}

fun main() -> float {
    return calcPi(1000.0);
}
```

* Interface- and class declaration syntax is shamelessly stolen from Java. The following shows how an interface is implemented, and class extension is provided using the ```extends``` keyword.

```javascript
interface BinOp {
    public fun apply(int a, int b) -> int;
}

class Plus implements BinOp {
    public fun apply(int a, int b) -> int {
        return a + b;
    }
}

fun main() -> int {
    BinOp plus = Plus();
    return plus.apply(1, 3);
}
```

## What is [not yet] implemented? ##
### Frontend ###
* Switch statements
* Exceptions

### Backend ###
* Various optimizations. The first passes to be written are
  * Constant propagation and constant folding
  * Common subexpression elimination
  * Tail recursion
  * Loop-invariant code motion
