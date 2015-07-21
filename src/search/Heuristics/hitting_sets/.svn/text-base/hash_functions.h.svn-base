#ifndef HASH_FUNCTIONS_H
#define HASH_FUNCTIONS_H

#include "bitmap_set.h"
#include <stdint.h>
#include <iostream>
#include <cassert>
#include <set>

namespace Hash {

// rotation
inline uint32_t rot(uint32_t x, uint32_t k) {
    return (x << k) | (x >> (32-k));
}

/*
-------------------------------------------------------------------------------
mix -- mix 3 32-bit values reversibly.

This is reversible, so any information in (a,b,c) before mix() is
still in (a,b,c) after mix().

If four pairs of (a,b,c) inputs are run through mix(), or through
mix() in reverse, there are at least 32 bits of the output that
are sometimes the same for one pair and different for another pair.
This was tested for:
* pairs that differed by one bit, by two bits, in any combination
  of top bits of (a,b,c), or in any combination of bottom bits of
  (a,b,c).
* "differ" is defined as +, -, ^, or ~^.  For + and -, I transformed
  the output delta to a Gray code (a^(a>>1)) so a string of 1's (as
  is commonly produced by subtraction) look like a single 1-bit
  difference.
* the base values were pseudorandom, all zero but one bit set, or 
  all zero plus a counter that starts at zero.

Some k values for my "a-=c; a^=rot(c,k); c+=b;" arrangement that
satisfy this are
    4  6  8 16 19  4
    9 15  3 18 27 15
   14  9  3  7 17  3
Well, "9 15 3 18 27 15" didn't quite get 32 bits diffing
for "differ" defined as + with a one-bit base and a two-bit delta.  I
used http://burtleburtle.net/bob/hash/avalanche.html to choose 
the operations, constants, and arrangements of the variables.

This does not achieve avalanche.  There are input bits of (a,b,c)
that fail to affect some output bits of (a,b,c), especially of a.  The
most thoroughly mixed value is c, but it doesn't really even achieve
avalanche in c.

This allows some parallelism.  Read-after-writes are good at doubling
the number of bits affected, so the goal of mixing pulls in the opposite
direction as the goal of parallelism.  I did what I could.  Rotates
seem to cost as much as shifts on every machine I could lay my hands
on, and rotates are much kinder to the top and bottom bits, so I used
rotates.
-------------------------------------------------------------------------------
*/
inline void mix(uint32_t &a, uint32_t &b, uint32_t &c) {
    a -= c;  a ^= rot(c, 4);  c += b;
    b -= a;  b ^= rot(a, 6);  a += c;
    c -= b;  c ^= rot(b, 8);  b += a;
    a -= c;  a ^= rot(c,16);  c += b;
    b -= a;  b ^= rot(a,19);  a += c;
    c -= b;  c ^= rot(b, 4);  b += a;
}

/*
-------------------------------------------------------------------------------
final -- final mixing of 3 32-bit values (a,b,c) into c

Pairs of (a,b,c) values differing in only a few bits will usually
produce values of c that look totally different.  This was tested for
* pairs that differed by one bit, by two bits, in any combination
  of top bits of (a,b,c), or in any combination of bottom bits of
  (a,b,c).
* "differ" is defined as +, -, ^, or ~^.  For + and -, I transformed
  the output delta to a Gray code (a^(a>>1)) so a string of 1's (as
  is commonly produced by subtraction) look like a single 1-bit
  difference.
* the base values were pseudorandom, all zero but one bit set, or 
  all zero plus a counter that starts at zero.

These constants passed:
 14 11 25 16 4 14 24
 12 14 25 16 4 14 24
and these came close:
  4  8 15 26 3 22 24
 10  8 15 26 3 22 24
 11  8 15 26 3 22 24
-------------------------------------------------------------------------------
*/
inline void final(uint32_t &a, uint32_t &b, uint32_t &c) {
    c ^= b;  c -= rot(b,14);
    a ^= c;  a -= rot(c,11);
    b ^= a;  b -= rot(a,25);
    c ^= b;  c -= rot(b,16);
    a ^= c;  a -= rot(c,4);
    b ^= a;  b -= rot(a,14);
    c ^= b;  c -= rot(b,24);
}

/*
--------------------------------------------------------------------
 This works on all machines.  To be useful, it requires
 -- that the key be an array of uint32_t's, and
 -- that the length be the number of uint32_t's in the key

 The function hashword() is identical to hashlittle() on little-endian
 machines, and identical to hashbig() on big-endian machines,
 except that the length has to be measured in uint32_ts rather than in
 bytes.  hashlittle() is more complicated than hashword() only because
 hashlittle() has to dance around fitting the key bytes into registers.
--------------------------------------------------------------------
*/
inline uint32_t hashword(const uint32_t *to_hash, size_t len, uint32_t initvalue) {
    uint32_t a,b,c;

    // Set up the internal state
    a = b = c = 0xdeadbeef + (len << 2) + initvalue;

    // handle most of the key
    while( len > 3 ) {
        a += to_hash[0];
        b += to_hash[1];
        c += to_hash[2];
        mix(a, b, c);
        len -= 3;
        to_hash += 3;
    }

    // handle the last 3 uint32_t's
    switch( len ) { 
        case 3 : c += to_hash[2];
        case 2 : b += to_hash[1];
        case 1 : a += to_hash[0];
            final(a, b, c);
        case 0:     // case 0: nothing left to add
            break;
    }

    return c;
}

struct SetUnsigned {
    size_t operator()(const std::set<unsigned> &to_hash) const {
        uint32_t a, b, c;
        size_t len = to_hash.size();

        // Set up the internal state
        a = b = c = 0xdeadbeef + (len << 2);

        // handle most of the key
        std::set<unsigned>::const_iterator it = to_hash.begin();
        while( len > 3 ) {
            a += *it++;
            b += *it++;
            c += *it++;
            mix(a, b, c);
            len -= 3;
        }

        // handle the last 3 uint32_t's
        if( len >= 1 ) a += *it++;
        if( len >= 2 ) b += *it++;
        if( len >= 3 ) c += *it++;
        assert(it == to_hash.end());

        // finish and return
        final(a, b, c);
        //std::cout << "hvalue=" << c << std::endl;
        return c;
    }
};

struct BitmapSet {
    size_t operator()(const Utils::BitmapSet &to_hash) const {
        uint32_t a, b, c;
        size_t len = to_hash.size();

        // Set up the internal state
        a = b = c = 0xdeadbeef + (len << 2);

        // handle most of the key
        Utils::BitmapSet::const_iterator it = to_hash.begin();
        while( len > 3 ) {
            a += *it++;
            b += *it++;
            c += *it++;
            mix(a, b, c);
            len -= 3;
        }

        // handle the last 3 uint32_t's
        if( len >= 1 ) a += *it++;
        if( len >= 2 ) b += *it++;
        if( len >= 3 ) c += *it++;
        assert(it == to_hash.end());

        // finish and return
        final(a, b, c);
        //std::cout << "hvalue=" << c << std::endl;
        return c;
    }
};

} // end of namespace

#endif
