#ifndef _hash_hpp_INCLUDED
#define _hash_hpp_INCLUDED

#include <cassert>
#include <vector>

namespace CaDiCaL {

// for debugging (we cannot use LOG)
// guard to avoid warnings.
// #define MYPRINTFLOGGING
#define MYPRINTF(...) // printf(__VA_ARGS__)

// This is a hash set that tries to follow (some of the) C++ interface
// without promising iterator stability, which is really reducing speed. It
// is missing the `equal_range ()` operations though.
//
// KeyEqualTmpDuplicates is used for temporary duplicates if you want to
// search except for one element that you has already changed its hash
// value, but you do not want to find.
//
// The hash table is mostly intended to contain pointers, hence it uses 0x01
// as tumb.
template <class Key, class Hash, class KeyEqual = std::equal_to<Key>,
          class KeyEqualTmpDuplicates = std::equal_to<Key>>
class hash {
public:
  using stored_pair = std::pair<size_t, Key>;

  class iterator {
  public:
    using iterator_category = std::random_access_iterator_tag;
    using value_type = Key;
    using difference_type =
        typename std::vector<stored_pair>::difference_type;
    using pointer = Key *;
    using reference = Key &;

    iterator () = default;

    iterator (const typename std::vector<stored_pair>::iterator &p)
        : ptr (p) {}
    iterator operator= (const stored_pair &p) {
      ptr->second = p.second;
      return *this;
    }

    reference &operator* () const { return ptr->second; }
    pointer operator->() const { return &(ptr->second); }
    stored_pair raw_value () const { return *ptr; }

    iterator &operator++ () {
      ++ptr;
      return *this;
    }

    iterator operator++ (int) {
      iterator tmp = *this;
      ++ptr;
      return tmp;
    }

    iterator &operator-- () {
      --ptr;
      return *this;
    }

    iterator operator-- (int) {
      iterator tmp = *this;
      --ptr;
      return tmp;
    }

    iterator operator+ (difference_type n) const {
      return iterator (ptr + n);
    }

    iterator operator- (difference_type n) const {
      return iterator (ptr - n);
    }

    iterator &operator+= (difference_type n) {
      ptr += n;
      return *this;
    }

    iterator &operator-= (difference_type n) {
      ptr -= n;
      return *this;
    }

    reference operator[] (difference_type n) const { return ptr[n].second; }

    friend bool operator== (const iterator &a, const iterator &b) {
      return a.ptr == b.ptr;
    }

    friend bool operator!= (const iterator &a, const iterator &b) {
      return a.ptr != b.ptr;
    }

    friend bool operator< (const iterator &a, const iterator &b) {
      return a.ptr < b.ptr;
    }

    friend bool operator> (const iterator &a, const iterator &b) {
      return a.ptr > b.ptr;
    }

    friend bool operator<= (const iterator &a, const iterator &b) {
      return a.ptr <= b.ptr;
    }

    friend bool operator>= (const iterator &a, const iterator &b) {
      return a.ptr >= b.ptr;
    }

    friend iterator operator+ (difference_type n, const iterator &it) {
      return it + n;
    }

    friend difference_type operator- (const iterator &a,
                                      const iterator &b) {
      return a.ptr - b.ptr;
    }

    friend class hash;

  private:
    typename std::vector<stored_pair>::iterator ptr;
  };

  const stored_pair tumb = std::make_pair<size_t, Key> (
      0, reinterpret_cast<const Key> ((void *) 1));

private:
  std::vector<stored_pair> table;
  Hash hasher;

public:
  hash () : hasher ({}) {};
  template <class T> hash (T h) : hasher (h) {
    table.resize (64, std::make_pair<size_t, Key> (0, nullptr));
  }
  iterator begin () { return iterator (table.begin ()); }

  iterator end () { return iterator (table.end ()); }

  iterator erase (Key el) {
    const size_t hash_val = hasher (el);
    size_t pos = reduce_hash (hash_val);
    size_t hash_size = table.size ();
    assert (entries);

    while (!KeyEqual (table[pos], el)) {
      ++collisions;
      if (++pos == hash_size)
        pos = 0;
    }
    assert (KeyEqual (table[pos], el));
    table[pos] = tumb;
    MYPRINTF ("deleting pos %d\n", pos);
    return iterator (table.begin () + pos + 1);
  }

  iterator erase (iterator git) {
    git.ptr->second = tumb.second;
    git.ptr->first = tumb.first;
    auto rit = git + 1;
    MYPRINTF ("overwriting second\n");
    return rit;
  }

  iterator find (Key el, Key except) {
    const size_t hash_val = hasher (el);
    const size_t start_pos = reduce_hash (hash_val);
    size_t pos = start_pos;
    MYPRINTF ("starting at position %zd with hash %zd\n", pos, hash_val);
    size_t hash_size = table.size ();
    stored_pair g;
    Key res{};

    while ((g = table[pos]), g.second) {
      MYPRINTF ("looking at position %zd, %zd vs %zd\n", pos, g.first,
                hash_val);
      if (g == tumb)
        ;
      else if (g.first != hash_val)
        ;
      else if (g.second == except)
        ;
      else if (KeyEqual () (g.second, el)) {
        res = g.second;
        MYPRINTF ("found id %zd at position %zd\n", g.second->id (), pos);
        break;
      }
      if (++pos == hash_size) {
        MYPRINTF ("reached the end\n");
        pos = 0;
      }
      if (pos == start_pos) {
        MYPRINTF ("reached the start again\n");
        break;
      }
    }
    if (!res) {
      MYPRINTF ("not found\n");
      return iterator (table.end ());
    }
    assert (res != tumb.second);
    return iterator (table.begin () + pos);
  }

  iterator find (Key el) {
    const size_t hash_val = hasher (el);
    const size_t start_pos = reduce_hash (hash_val);
    size_t pos = start_pos;
    MYPRINTF ("starting at position %zd with hash %zd\n", pos, hash_val);
    size_t hash_size = table.size ();
    stored_pair g;
    Key res{};

    while ((g = table[pos]), g.second) {
      MYPRINTF ("looking at position %zd, %zd vs %zd\n", pos, g.first,
                hash_val);
      if (g == tumb)
        ;
      else if (g.first != hash_val)
        ;
      else if (KeyEqual () (g.second, el)) {
        res = g.second;
        MYPRINTF ("found id %zd at position %zd\n", g.second->id (), pos);
        break;
      }
      if (++pos == hash_size) {
        MYPRINTF ("reached the end\n");
        pos = 0;
      }
      if (pos == start_pos) {
        MYPRINTF ("reached the start again\n");
        break;
      }
    }
    if (!res) {
      MYPRINTF ("not found\n");
      return iterator (table.end ());
    }
    assert (res != tumb.second);
    return iterator (table.begin () + pos);
  }

  iterator insert (Key el) {
    if (is_full ())
      resize_hash_table ();
    const size_t hash_val = hasher (el);
    const size_t start_pos = reduce_hash (hash_val);
    size_t pos = start_pos;
    stored_pair g;
    size_t hash_size = table.size ();
    MYPRINTF ("trying to insert at position %zd\n", pos);
    ++entries;

    while ((g = table[pos]), g.second) {
      MYPRINTF ("looking at position %zd, %zd vs %zd\n", pos, g.first,
                hash_val);
      if (g == tumb) {
        break;
      }
      ++collisions;
      if (++pos == hash_size)
        pos = 0;
      assert (pos < table.size ());
      assert (pos != start_pos);
    }
    table[pos].second = el;
    table[pos].first = hash_val;
    MYPRINTF ("insert %zd at position %zd with hash %zd\n", el->id (), pos,
              hash_val);
    return iterator (table.begin () + pos);
  }

  size_t count (Key el) {
    if (find (el) != end ())
      return 1;
    return 0;
  }

#if 0
  // buggy due to wrapping around end
  std::pair<iterator, iterator> equal_range(Key const& key)
  {
    iterator pos = find(key);
    if (pos == end()) {
      return make_pair (pos, pos);
    }

    iterator next = pos;
    while (*next && next.raw_value() != removed)
      ++next;
    return make_pair (pos, next);
  }
#endif

  void clear () { table.clear (); };

private:
  size_t collisions = 0;
  size_t entries = 0;
  size_t reduce_hash (size_t hash, size_t other_size, size_t other_size2) {
    assert (other_size);
    size_t res = hash;
    res &= other_size2 - 1;
    if (res >= other_size)
      res -= other_size;
    assert (res < other_size);
    return res;
  }
  size_t reduce_hash (size_t hash) {
    return reduce_hash (hash, table.size (), table.size ());
  }
  size_t reduce_hash (size_t hash, size_t size) {
    return reduce_hash (hash, size, size);
  }

  void resize_hash_table () {
    MYPRINTF ("resize\n");
    decltype (table) new_table;
    size_t new_size = 2 * table.size ();
    new_table.resize (new_size, std::make_pair<size_t, Key> (0, nullptr));
    const size_t old_entries = entries;
    size_t flushed = 0;
#ifdef MYPRINTFLOGGING
    auto old_pos = 0;
#endif

    for (auto el : table) {
      if (!el.second) {
#ifdef MYPRINTFLOGGING
        ++old_pos;
#endif
        continue;
      }
      if (el == tumb) {
        ++flushed;
#ifdef MYPRINTFLOGGING
        ++old_pos;
#endif
        continue;
      }

      size_t new_pos = reduce_hash (el.first, new_size);
      while (new_table[new_pos].second) {
        if (++new_pos == new_size)
          new_pos = 0;
      }
      new_table[new_pos] = el;
#ifdef MYPRINTFLOGGING
      MYPRINTF (
          "inserting id %zd at position %zd was at %zd, with hash %zd\n",
          el.second->id (), new_pos, old_pos, el.first);
      ++old_pos;
#endif
    }

    table = std::move (new_table);
    entries = old_entries - flushed;
    MYPRINTF ("end of resize\n");
  }

  bool is_full () const {
    if (2 * entries < table.size ())
      return false;
    return true;
  }
};

} // namespace CaDiCaL
#endif
