# Brilt

Work in progress [Bril](https://github.com/sampsyo/bril) to RVSDG library.

# Usage

There are some optimizations defined in `schema.egg`

```
❯ cat bril/examples/test/df/cond.bril | tee /dev/stderr | bril2json | cargo run | bril2txt 
@main {
  a: int = const 47;
  b: int = const 42;
  cond: bool = const true;
  br cond .left .right;
.left:
  b: int = const 1;
  c: int = const 5;
  jmp .end;
.right:
  a: int = const 2;
  c: int = const 10;
  jmp .end;
.end:
  d: int = sub a c;
  print d;
}
   Compiling brilt v0.1.0 (/home/hatoo/brilt)
    Finished dev [unoptimized + debuginfo] target(s) in 3.12s
     Running `target/debug/brilt`
@main {
  v0: int = const 42;
  print v0;
  ret;
}
```