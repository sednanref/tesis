#ifndef BITMAP_SET_H
#define BITMAP_SET_H

#include <iostream>
#include <vector>
#include <limits>
#include <strings.h>

namespace Utils {

struct BitmapSet {
    unsigned *bitmap_;
    unsigned size_;

    BitmapSet() {
        bitmap_ = new unsigned[dim_];
        clear();
    }
    BitmapSet(const BitmapSet &bset) {
        bitmap_ = new unsigned[dim_];
        *this = bset;
    }
    ~BitmapSet() { delete[] bitmap_; }

    void clear() {
        bzero(bitmap_, dim_*sizeof(unsigned));
        size_ = 0;
    }

    unsigned size() const { return size_; }
    bool empty() const { return size_ == 0; }

    void insert(int index) {
        int off = index>>5, bit = (index-(off<<5));
        if( !((bitmap_[off]>>bit) & 0x1) ) {
            bitmap_[off] |= 1<<bit;
            ++size_;
        }
    }
    void insert(const BitmapSet &bset) {
        for( const_iterator i = bset.begin(); i != bset.end(); ++i )
            insert(*i);
    }

    void erase(int index) {
        int off = index>>5, bit = (index-(off<<5));
        if( (bitmap_[off]>>bit) & 0x1 ) {
            bitmap_[off] &= ~(1<<bit);
            --size_;
        }
    }
    void erase(const BitmapSet &bset) {
        for( const_iterator i = bset.begin(); i != bset.end(); ++i )
            erase(*i);
    }

    bool is_contained_in(const BitmapSet &bset) const {
        return bset.contains(*this);
    }
    bool contains(const BitmapSet &bset) const {
        for( int off = 0; off < dim_; ++off ) {
            if( (bset.bitmap_[off]&~(bitmap_[off])) != 0 )
                return false;
	}
	return true;
    }
    bool contains(int index) const {
        int off = index>>5, bit = (index-(off<<5));
        return (((bitmap_[off]>>bit)&0x1) == 1);
    }

    bool empty_intersection(const BitmapSet &bset) const {
        for( const_iterator it = begin(); it != end(); ++it ) {
            if( bset.contains(*it) ) return false;
        }
        return true;
    }

    bool operator==(const BitmapSet &bset) const {
        return (size_ == bset.size_) && contains(bset);
    }
    bool operator!=(const BitmapSet &bset) const {
        return !(*this == bset);
    }
    const BitmapSet& operator=(const BitmapSet &bset) {
        clear();
        for( int off = 0; off < dim_; ++off )
            bitmap_[off] = bset.bitmap_[off];
        size_ = bset.size_;
        return *this;
    }

    void print(std::ostream &os) const {
        os << "{";
        for( const_iterator si = begin(); si != end(); ++si )
            os << *si << ",";
        os << "}";
    }

    struct const_iterator {
        const unsigned *bitmap_;
        int off_, bit_;

	const_iterator(const unsigned *bitmap_ = 0, int off = 0, int bit = 0)
          : bitmap_(bitmap_), off_(off), bit_(bit) { }
	~const_iterator() { }

	const const_iterator& operator++() {
            ++bit_;
	    if( (bit_ < 32) && (bitmap_[off_]>>bit_) != 0 ) {
                for( unsigned word = bitmap_[off_]>>bit_; (word&0x1) == 0; word = word>>1, ++bit_ ) ;
	    }
	    else {
                bit_ = 0;
                for( ++off_; (off_ < dim_) && (bitmap_[off_] == 0); ++off_ ) ;
                if( off_ < dim_ ) {
                    for( unsigned word = bitmap_[off_]; (word&0x1) == 0; word = word>>1, ++bit_ ) ;
		}
	    }
	    return *this;
	}
        const const_iterator& operator++(int) { return ++(*this); }

        bool operator==(const const_iterator &it) const {
            return (off_ == it.off_) && (bit_ == it.bit_);
        }
	bool operator!=(const const_iterator &it) const {
            return (off_ != it.off_) || (bit_ != it.bit_);
        }

	int operator*() const { return (off_<<5)+bit_; }
	void print(std::ostream &os) const {
            os << "[" << off_ << "," << bit_ << "]";
        }
    };

    const_iterator begin() const {
        int off = 0, bit = 0;
        while( (off < dim_) && (bitmap_[off] == 0) ) ++off;
	if( off < dim_ ) {
            for( unsigned word = bitmap_[off]; ((word&0x1) == 0); word = word>>1, ++bit ) ;
	}
	return const_iterator(bitmap_,off,bit);
    }
    const_iterator end() const { return const_iterator(0, dim_, 0); }

    // hash function (defined below)
    size_t hash_function() const;

    static int dim_;
    static void initialize(int num_indices) {
        dim_ = num_indices >> 5;
        if( num_indices % 32 != 0 )
            ++dim_;
        std::cout << "Initializing BitmapSet:"
                  << " num_indices=" << num_indices
                  << ", dim=" << dim_ << std::endl;
    }
};

} // end of namespace

#include "hash_functions.h"

namespace Utils {
    inline size_t BitmapSet::hash_function() const {
        return Hash::BitmapSet()(*this);
    }
}

#include <tr1/functional>

namespace std {
    namespace tr1 {
        template<> struct hash<Utils::BitmapSet> {
            size_t operator()(const Utils::BitmapSet &bset) const {
                return bset.hash_function();
            }
        };
    } // end of namespace
} // end of namespace

#endif

