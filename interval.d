#!/usr/local/bin/dmd -debug -unittest -main -run
module interval;

debug import std.stdio;
private import std.math;


enum Bound : bool { closed, open }


/// General interval of floats
struct Interval(F)
  if (__traits(isFloating, F))
{
  F lo, hi;
  Bound lob = Bound.open;
  Bound hib = Bound.open;

  invariant { assert(lo <= hi || isNaN(lo) || isNaN(hi) || lo == F.infinity || hi == -F.infinity); }

  this(in F f) { this.lo = this.hi = f; lob = hib = isNaN(f)?Bound.open:Bound.closed; }
  this(in F l, in Bound lb, in F h, in Bound hb) { lo = l; lob = lb; hi = h; hib = hb; }

  enum nan = Interval!F.init;
  enum empty = Interval!F(F.infinity, Bound.closed, -F.infinity, Bound.closed);
  enum allReals = Interval!F(-F.infinity, Bound.closed, F.infinity, Bound.closed);
  enum posReals = Interval!F(0, Bound.closed, F.infinity, Bound.closed);
  enum negReals = Interval!F(-F.infinity, Bound.closed, 0, Bound.closed);

  bool isEmpty() pure const @property { return lo == F.infinity || hi == -F.infinity; }

  string toString() const
  {
    import std.conv;
    return (lob?'(':'[')~to!string(lo)~','~to!string(hi)~(hib?')':']');
  }

  auto opBinary(string S)(Interval!F rhs) const pure
    if (S == "-")
  {
    return this + (-rhs);
  }

  auto opBinary(string S)(Interval!F rhs) const pure
    if (S == "+")
  {
    if (lo.isNaN || hi.isNaN || rhs.lo.isNaN || rhs.hi.isNaN)
      return nan;

    Interval!F result;
    if (lo == -F.infinity && !lob) {
      if (rhs.lo == F.infinity && !rhs.lob){//empty?
        result.lo = F.nan;
        result.lob = Bound.open;
      }
      else {
        result.lo = -F.infinity;
        result.lob = Bound.closed;
      }
    }
    else if (rhs.lo == -F.infinity && !rhs.lob) {
      if (lo == F.infinity && !lob) {//empty?
        result.lo = F.nan;
        result.lob = Bound.open;
      }
      else {
        result.lo = -F.infinity;
        result.lob = Bound.closed;
      }
    }
    else if ((lo == F.infinity && !lob) || (rhs.lo == F.infinity && !rhs.lob)) {
      result.lo = F.infinity;//empty
      result.lob = Bound.closed;
    }
    else if (lo == -F.infinity) {
      if  (rhs.lo == F.infinity && !rhs.lob) {//empty?
        result.lo = F.infinity;//empty
        result.lob = Bound.closed;
      }
      else {
        result.lo = -F.infinity;
        result.lob = Bound.open;
      }
    }
    else if (rhs.lo == -F.infinity) {
      if (lo == F.infinity && !lob) {//empty?
        result.lo = F.infinity;//empty
        result.lob = Bound.closed;
      }
      else {
        result.lo = -F.infinity;
        result.lob = Bound.open;
      }
    }
    else {
      result.lo = lo + rhs.lo;
      result.lob = cast(Bound)(lob || rhs.lob);
    }

    if (hi == -F.infinity && !hib) {//empty?
      if (rhs.hi == F.infinity && !rhs.hib){
        result.hi = F.nan;
        result.hib = Bound.open;
      }
      else {
        result.hi = -F.infinity;
        result.hib = Bound.closed;
      }
    }
    else if (rhs.hi == -F.infinity && !rhs.hib) {//empty?
      if (hi == F.infinity && !hib) {
        result.hi = F.nan;
        result.hib = Bound.open;
      }
      else {
        result.hi = -F.infinity;//empty
        result.hib = Bound.closed;
      }
    }
    else if ((hi == F.infinity && !hib) || (rhs.hi == F.infinity && !rhs.hib)) {
      result.hi = F.infinity;
      result.hib = Bound.closed;
    }
    else if (hi == F.infinity) {
      if  (rhs.hi == -F.infinity && !rhs.hib) {//empty?
        result.hi = -F.infinity;//empty
        result.hib = Bound.closed;
      }
      else {
        result.hi = F.infinity;
        result.hib = Bound.open;
      }
    }
    else if (rhs.hi == F.infinity) {
      if (hi == -F.infinity && !hib) {//empty?
        result.hi = -F.infinity;//empty
        result.hib = Bound.closed;
      }
      else {
        result.hi = F.infinity;
        result.hib = Bound.open;
      }
    }
    else {
      result.hi = hi + rhs.hi;
      result.hib = cast(Bound)(hib || rhs.hib);
    }
    return result;
  }

  bool opEquals(in Interval!F rhs) const pure
  {
    return this.lo is rhs.lo && this.hi is rhs.hi && this.lob == rhs.lob && this.hib == rhs.hib;
  }

  auto opUnary(string S)() const pure
    if (S == "+")
  {
    return this;
  }

  auto opUnary(string S)() const pure
    if (S == "-")
  {
    return Interval!F(-hi, hib, -lo, lob);
  }

  auto opBinary(string S)(in Interval!F rhs) const pure
    if (S == "|")
  {
    if (lo.isNaN || hi.isNaN || rhs.lo.isNaN || rhs.hi.isNaN)
      return nan;
    if (lo < rhs.lo || (lo == rhs.lo && rhs.lob))
    {

    }
    if (lo < rhs.hi || (lo == rhs.hi && !lob && !rhs.hib))
    {

    }
    return nan;
  }

  auto abs() pure const @property
  {
    if (isNaN(lo) || isNaN(hi))
      return nan;
    if (hi <= 0.0)
      return Interval!F(fabs(hi), hib, fabs(lo), lob);
    if (lo <= 0.0)
    {
      F abslo = fabs(lo);
      F abshi = fabs(hi);
      if (abslo < abshi)
        return Interval!F(0, Bound.closed, abshi, hib);
      if (abslo > abshi)
        return Interval!F(0, Bound.closed, abslo, lob);
      return Interval!F(0, Bound.closed, abslo, cast(Bound)(lob && hib));
    }
    return Interval!F(lo, lob, hi, hib);
  }

}




private auto all() pure {
  Interval!float[] result;
  enum array = [float.nan, -float.infinity, -0.0, 100, float.infinity];
  foreach (k, l; array)
    foreach (lb; [Bound.open, Bound.closed])
      foreach(h; array[k..$])
        foreach (hb; [Bound.open, Bound.closed])
          result ~= Interval!float(l, lb, h, hb);
  return result;
}


unittest
{
  static assert(Interval!float.empty.isEmpty);

  foreach (x; all()) {
    assert(x == +x);
    foreach (y; all()) {
      writeln(x, "+", y, "=", x + y);
      writeln(x, "-", y, "=", x - y);
      assert(-y + x == x - y);
      assert(x + y == y + x);
    }
  }
}
