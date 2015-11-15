module unum;
debug import std.stdio;
private import std.math;

template union_cast(T)
{
  T union_cast(F)(in F from) pure if (F.sizeof == T.sizeof)
  {
    union X { F f; T t; }
    X x = {from};
    return x.t;
  }
}

unittest
{
  assert(union_cast!float(0) == 0.0f);
  assert(union_cast!int(0.0f) == 0);
}


enum Ubit { exact, inexact }


/// Fixed sized Unum using a native floating point type F as storage
struct Unum(F) if (__traits(isFloating, F))
{
  static assert(Unum.sizeof == F.sizeof);
  static assert(Unum.alignof == F.alignof);

  private enum oo2log10 = 0.3010f;

  union
  {
    F value;
    static if (F.mant_dig == 24)
      uint utag;
    static if (F.mant_dig == 53)
      ulong utag;
    static if (F.mant_dig == 64)
      struct { ulong utag; ushort utaghi; }
    static if (F.mant_dig == 113)
      struct { ulong utag; ulong utaghi; }
  }

  // Traits:

  enum precbits = F.mant_dig <= 32 ? 5U : F.mant_dig <= 64 ? 6U : 7U;//log2
  enum utagbits = precbits + 1;
  enum max_mant_dig = F.mant_dig - utagbits;
  enum UBIT = (cast(typeof(utag))1U)<<precbits;
  enum UFRACMASK = UBIT-1;
  enum ULP = UBIT<<1;
  enum UTAGMASK = ULP-1;

  invariant { assert((utag & UFRACMASK) <= max_mant_dig || isNaN(value)); }

  /// Create Unum from exact integer
  private import core.bitop : bsr;
  this(I)(I i) if (__traits(isIntegral, I))
  {
    auto b = cast(ubyte)(1 + bsr(i<0?-i:i));//cast should not be necessary
    assert(b <= max_mant_dig);
    this.value = i;
    this.utag = (this.utag & ~UTAGMASK) | b;
  }

  /// Create Unum from floating point, with given precision
  this(F v, Ubit u, ubyte exp)
  in {
    assert(exp <= max_mant_dig);
  }
  body {
    this.value = v;
    this.utag = (this.utag & ~UTAGMASK) | (u?UBIT:0) | exp;
  }

  // Private constructor that wraps a floating point value
  private this(I)(in I v) if (is(I == F)) { this.value = v; }

  // Properties from float/double/real

  enum nan = Unum!F(F.nan);
  enum infinity = Unum!F(F.infinity);
  ubyte mant_dig() pure const @property { return utag&UFRACMASK; }
  ubyte mant_dig(ubyte p) pure @property { assert(p <= max_mant_dig); utag = (utag & ~UFRACMASK) | p; return p;}
  int dig() pure const @property { return cast(int)((mant_dig - 1) * oo2log10); }
  F epsilon() pure const @property { return std.math.exp2(1 - mant_dig); }

  // Properties specific to Unum

  typeof(this) exact() pure @property { auto t = this; t.utag &= ~UBIT; assert(t.isexact); return t; }
  bool isexact() pure const @property { return (utag&UBIT) == 0; }
  Ubit ubit() pure const @property { return (utag&UBIT)?Ubit.inexact:Ubit.exact; }
  Ubit ubit(Ubit u) pure @property { if (u) utag|=UBIT; else utag&=~UBIT; return u; }

  private auto _ulp() pure const @property { return (cast(typeof(utag))1)<<(F.mant_dig - mant_dig); }
  private F _realUpper() pure @property
  {
    auto t = Unum!F(lower);
    t.utag += _ulp;
    // TODO: detect fraction overflow
    return t.value;
  }

  F lower() pure @property { auto t = this; t.utag &= ~(_ulp-1); return t.value; }
  F upper() pure @property { return isexact ? lower : _realUpper; }
  F ulp() pure @property { return _realUpper - lower; }

  auto opUnary(string S)() pure const { mixin("return Unum!F("~S~"value);"); }

  auto opBinary(string S)(Unum!F rhs) pure if (S == '+')
  {
    Ubound!F lhs = this;
    Ubound!F r = rhs;
    Ubound!F t = lhs + rhs;
    return t.unum;
  }
}

alias ufloat = Unum!float;
alias udouble = Unum!double;
alias ureal = Unum!real;


enum Bound { close, open }


struct Ubound(F)
{
  Unum!F lo, hi;

  invariant { assert( lo.value <= hi.value); }

  this(Unum!F x) { this.lo = x.lower; this.hi = x.upper; }
  this(Unum!F lo, Unum!F hi) { this.lo = lo; this.hi = hi; }

  Bound boundLo() @property { return cast(Bound)lo.ubit; }
  Bound boundHi() @property { return cast(Bound)hi.ubit; }

  auto opBinary(string S)(Ubound!F rhs) if (S == "+")
  {
    UBound!F r;
    r.lo = this.lo.value + rhs.lo.value;
    r.hi = this.hi.value + rhs.hi.value;
    return r;
  }

  // Create Unum from Ubound
}

unittest
{
  ufloat uf = 1;
  Ubound!float ub = uf;
  ufloat uf2 = ufloat(0.33, Ubit.inexact, 6);
  Ubound!float ub2 = uf2;
}

//TODO
//bool isNaN(U)(in U u) if (is(U : Unum!F, alias F)) { return isNaN(u.value); }

unittest
{
  Unum!(float) uf;
  Unum!(double) ud;
  Unum!(real) ur;

  //assert(isNaN(uf));
  //assert(uf.isNaN);
  //assert(ud.isNaN);
  //assert(ur.isNaN);
  ud.ubit = ur.ubit = uf.ubit = Ubit.exact;
  assert(uf.ubit == Ubit.exact);
  assert(ud.ubit == Ubit.exact);
  assert(ur.ubit == Ubit.exact);
  ud.ubit = ur.ubit = uf.ubit = Ubit.inexact;
  assert(uf.ubit == Ubit.inexact);
  assert(ud.ubit == Ubit.inexact);
  assert(ur.ubit == Ubit.inexact);
  uf.mant_dig = 11;
  assert(uf.mant_dig == 11);
  assert(uf.dig == 3);
  ud.mant_dig = 22;
  assert(ud.mant_dig == 22);
  assert(ud.dig == 6);
  ur.mant_dig = 55;
  assert(ur.mant_dig == 55);
  assert(ur.dig == 16);
  assert(ur.exact.ubit == Ubit.exact);
}

unittest
{
  import std.meta;
  foreach (T; AliasSeq!(float, double, real))
  {
    enum T v = 1/3.0;
    foreach (const p; 2..Unum!T.max_mant_dig+1)
    {
      Unum!T u = Unum!T(v, Ubit.inexact, p);
      assert(u.lower < v);
      assert(v < u.upper);
    }
  }
}

unittest
{
  Unum!float uf = -0x3FFFF;//18bits
  assert(uf.mant_dig == 18);
  assert(uf.ubit == Ubit.exact);
  assert(uf.isexact);
  assert(uf.lower == -0x3FFFF);
  assert(uf.lower == uf.upper);

  assert((+uf).value ==  uf.value);
  assert((-uf).value == -uf.value);

  Unum!float uf2 = 0x3FFFF;//18bits
  assert(uf2.mant_dig == 18);
  uf2.ubit = Ubit.inexact;
  assert(uf2.lower == 0x3FFFF);
  assert(uf2.ulp == 1);
  assert(uf2.upper == 0x40000);
  assert(uf2.upper - uf2.lower == 1);

  Unum!float avogardo = Unum!float(6.022E23, Ubit.inexact, 12);

  Unum!float half = Unum!float(0.5f, Ubit.exact, 2);
  assert(half.ulp == 0.25);
  //static assert(!__traits(compiles, {Unum!float u = 0x40000;}));
}

void main()
{
  import std.stdio;
}

