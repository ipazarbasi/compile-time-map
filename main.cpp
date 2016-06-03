// Compile-time map, made after Dietmar Kuhl's session at ACCU 2016.
// Feel free to use it, and please let me know if you find an interesting
// way to use it.

#if __cplusplus > 201103L
#include <array>
#endif

#include <iterator>
#include <stdio.h>
#include <type_traits>

namespace constexpr_stuff {
struct string_view {
  constexpr string_view(const char *p, size_t s) : p(p), s(s) {}
  constexpr string_view() : p(), s() {}
  constexpr int compare(const string_view &other) const;
  constexpr int compare_impl(const char *p, const char *q, size_t n) const;
  constexpr const char *data() const { return p; }
  constexpr size_t size() const { return s; }

private:
  const char *p;
  size_t s;
};
constexpr bool operator<(const string_view &a, const string_view &b) {
  return a.compare(b) < 0;
}
constexpr bool operator==(const string_view &a, const string_view &b) {
  return a.compare(b) == 0;
}
namespace udl {
constexpr constexpr_stuff::string_view operator""_sv(const char *p, size_t s) {
  return constexpr_stuff::string_view(p, s);
}
}

#if __cplusplus == 201103L
// min
inline namespace cxx14_compat {
template <typename T> constexpr const T &min(const T &a, const T &b) {
  return a < b ? a : b;
}

// enable_if_t
template <bool b, class T = void>
using enable_if_t = typename std::enable_if<b, T>::type;

template <class... _Tp>
using common_type_t = typename std::common_type<_Tp...>::type;

template <typename T>
inline constexpr T &&
forward(typename std::remove_reference<T>::type &t) noexcept {
  return static_cast<T &&>(t);
}

template <typename T>
inline constexpr T &&
forward(typename std::remove_reference<T>::type &&t) noexcept {
  static_assert(!std::is_lvalue_reference<T>::value,
                "Can not forward an rvalue as an lvalue.");
  return static_cast<T &&>(t);
}

template <typename T = void> struct less {
  constexpr bool operator()(const T &x, const T &y) const { return x < y; }
};
template <> struct less<void> {
  template <typename ATy, typename BTy>
  constexpr bool operator()(ATy &&a, BTy &&b) const
      noexcept(noexcept(constexpr_stuff::forward<ATy>(a) <
                        constexpr_stuff::forward<BTy>(b))) {
    return constexpr_stuff::forward<ATy>(a) < constexpr_stuff::forward<BTy>(b);
  }
  typedef void is_transparent;
};

// index sequence - taken from Xeo's answer on stackoverflow
template <typename T, T... Ts> struct integer_sequence {
  using type = integer_sequence;
};
template <size_t... Ns> using index_sequence = integer_sequence<size_t, Ns...>;
template <typename T> using Type = typename T::type;
template <typename T0, typename T1> struct append_seq;
template <size_t... Range0, size_t... Range1>
struct append_seq<index_sequence<Range0...>, index_sequence<Range1...>>
    : public index_sequence<Range0..., (sizeof...(Range0) + Range1)...> {};

template <typename Range0, typename Range1>
using AppendSeq = Type<append_seq<Range0, Range1>>;

template <size_t N> struct gen_seq;
template <size_t N> using GenSeq = Type<gen_seq<N>>;

template <size_t N>
struct gen_seq : AppendSeq<GenSeq<N / 2>, GenSeq<N - (N / 2)>> {};
template <> struct gen_seq<0> : index_sequence<> {};
template <> struct gen_seq<1> : index_sequence<0> {};

template <size_t N> using make_index_sequence = Type<gen_seq<N>>;

// array
template <typename T, size_t N> struct array {
  T elems[N > 0 ? N : 1];
  typedef const T *const_iterator;

  constexpr const T &operator[](size_t c) const noexcept { return elems[c]; }
  constexpr const_iterator begin() const noexcept {
    return const_iterator(elems);
  }
  constexpr const_iterator end() const noexcept {
    return const_iterator(elems + N);
  }
};

// pair
template <typename FirstTy, typename SecondTy> struct pair {
  typedef FirstTy first_type;
  typedef SecondTy second_type;

  FirstTy first;
  SecondTy second;
  constexpr pair() : first(), second() {}
  constexpr pair(const FirstTy &first, const SecondTy &second)
      : first(first), second(second) {}
};

template <class FirstTy, class SecondTy>
constexpr bool operator==(const pair<FirstTy, SecondTy> &a,
                          const pair<FirstTy, SecondTy> &b) {
  return a.first == b.first && a.second == b.second;
}

template <class FirstTy, class SecondTy>
constexpr bool operator!=(const pair<FirstTy, SecondTy> &a,
                          const pair<FirstTy, SecondTy> &b) {
  return !(a == b);
}

template <class FirstTy, class SecondTy>
constexpr bool operator<(const pair<FirstTy, SecondTy> &a,
                         const pair<FirstTy, SecondTy> &b) {
  return a.first < b.first || (!(b.first < a.first) && a.second < b.second);
}

template <class FirstTy, class SecondTy>
constexpr bool operator>(const pair<FirstTy, SecondTy> &a,
                         const pair<FirstTy, SecondTy> &b) {
  return b < a;
}

template <class FirstTy, class SecondTy>
constexpr bool operator>=(const pair<FirstTy, SecondTy> &a,
                          const pair<FirstTy, SecondTy> &b) {
  return !(a < b);
}

template <class FirstTy, class SecondTy>
constexpr bool operator<=(const pair<FirstTy, SecondTy> &a,
                          const pair<FirstTy, SecondTy> &b) {
  return !(b < a);
}
} // cxx14_compat

#else
using std::array;
using std::index_sequence;
using std::make_index_sequence;
using std::enable_if_t;
using std::common_type_t;
using std::less;
using std::pair;
using std::forward;
using std::min;
#endif

// Taken from Richard Smith's post to cfe-dev
constexpr int string_view::compare_impl(const char *p, const char *q,
                                        size_t n) const {
  return !n ? 0
            : *p != *q ? *p - *q : !*p ? 0 : compare_impl(p + 1, q + 1, n - 1);
}
constexpr int
string_view::compare(const constexpr_stuff::string_view &other) const {
  return compare_impl(data(), other.data(),
                      constexpr_stuff::min(size(), other.size()));
}

// distance
template <typename InputIter>
constexpr typename std::iterator_traits<InputIter>::difference_type
distance_impl(const InputIter &first, const InputIter &last,
              std::input_iterator_tag) {
  return first == last
             ? 0
             : distance_impl(first + 1, last, std::input_iterator_tag()) + 1;
}

template <typename InputIter>
constexpr typename std::iterator_traits<InputIter>::difference_type
distance_impl(const InputIter &first, const InputIter &last,
              std::random_access_iterator_tag) {
  return last - first;
}
template <typename Iter>
constexpr typename std::iterator_traits<Iter>::difference_type
distance(const Iter &first, Iter last) {
  return distance_impl(
      first, last, typename std::iterator_traits<Iter>::iterator_category());
}

template <typename InputIter>
constexpr InputIter
next_impl(const InputIter &iter,
          typename std::iterator_traits<InputIter>::difference_type n,
          std::input_iterator_tag) {
  return n < 0 ? throw "input iterators can go only forward"
               : n == 0 ? iter : next_impl(iter + 1, n - 1);
}

template <typename RandomAccessIter>
constexpr RandomAccessIter
next_impl(const RandomAccessIter &iter,
          typename std::iterator_traits<RandomAccessIter>::difference_type n,
          std::random_access_iterator_tag) {
  return iter + n;
}

// next
template <typename IterTy>
constexpr IterTy
next(const IterTy &it,
     typename std::iterator_traits<IterTy>::difference_type n = 1) {
  return next_impl(it, n,
                   typename std::iterator_traits<IterTy>::iterator_category());
}

// select_array_range
template <typename T, size_t N, size_t... I>
constexpr array<T, sizeof...(I)>
select_array_range(const array<T, N> &a,
                   constexpr_stuff::index_sequence<I...>) {
  return array<T, sizeof...(I)>{a[I]...};
}

template <size_t Range0, size_t... I>
constexpr auto mkseq(constexpr_stuff::index_sequence<I...>)
    -> constexpr_stuff::index_sequence<(Range0 + I)...> {
  return constexpr_stuff::index_sequence<(Range0 + I)...>{};
}

// mkseq - indices start from Range0, not 0.
template <size_t Range0, size_t RangeN>
constexpr auto mkidxs()
    -> decltype(mkseq<Range0>(constexpr_stuff::make_index_sequence<RangeN>())) {
  return mkseq<Range0>(constexpr_stuff::make_index_sequence<RangeN>());
}

template <typename T, size_t N> constexpr array<T, N - 1u> tail(array<T, N> a) {
  return select_array_range(a, mkidxs<1u, N - 1u>());
}

template <typename T, size_t N, size_t... I>
constexpr array<T, N + 1u> construct_(T v, const array<T, N> &a,
                                      constexpr_stuff::index_sequence<I...>) {
  return array<T, N + 1u>{{v, a[I]...}};
}

template <typename T, size_t N>
constexpr array<T, N + 1u> construct(T v, const array<T, N> &a) {
  return construct_(v, a, mkidxs<0, N>());
}

template <typename T, size_t N>
constexpr array<T, N> merge_impl(array<T, 0>, array<T, N> a) {
  return a;
}
template <typename T, size_t N>
constexpr array<T, N> merge_impl(array<T, N> a, array<T, 0>) {
  return a;
}

template <typename T, size_t N1, size_t N2>
constexpr array<T, N1 + N2> merge_impl(const array<T, N1> &a1,
                                       const array<T, N2> &a2) {
  return a1[0] < a2[0] ? construct(a1[0], merge_impl(tail(a1), a2))
                       : construct(a2[0], merge_impl(a1, tail(a2)));
}

// msort - merge sort
template <typename T, size_t N,
          typename = constexpr_stuff::enable_if_t<!(1u < N)>, typename = void>
constexpr array<T, N> msort(const array<T, N> a) {
  return a;
}

template <typename T, size_t N, typename = constexpr_stuff::enable_if_t<1u < N>>
constexpr array<T, N> msort(const array<T, N> a) {
  return merge_impl(msort(select_array_range(a, mkidxs<0, (N + 1) / 2>())),
                    msort(select_array_range(a, mkidxs<(N + 1) / 2, N / 2>())));
}

template <typename IterTy, typename Comp>
constexpr IterTy adjacent_find(const IterTy &first, const IterTy &last,
                               Comp comp = Comp()) {
  return first == last || first + 1 == last
             ? last
             : comp(*first, *(first + 1))
                   ? first
                   : constexpr_stuff::adjacent_find(first + 1, last, comp);
}

template <typename KeyT, typename ValueT, size_t N,
          typename KeyComp = constexpr_stuff::less<KeyT>>
class map {
  using pair_type = constexpr_stuff::pair<KeyT, ValueT>;
  using array_type = array<pair_type, N>;
  using const_iterator = typename array_type::const_iterator;

  array_type values;

  template <typename Comp> struct equal_to1st_pred {
    template <typename PairTy>
    constexpr bool operator()(const PairTy &a, const PairTy &b) const {
      return !(Comp()(a.first, b.first)) && !(Comp()(b.first, a.first));
    }
  };

  template <typename Comp>
  constexpr equal_to1st_pred<Comp> equal_to1st() const {
    return equal_to1st_pred<Comp>{};
  }

  constexpr const_iterator is_key_found(const const_iterator &first,
                                        const const_iterator &last) const {
    return first == last ? throw "key not found in the map" : first;
  }

  template <typename ValueTy>
  constexpr const_iterator find_key_if_impl(const_iterator first,
                                            const_iterator last,
                                            const ValueTy &value) const {
    return (!(first == last) && !(key_comp()(value, first->first))) ? first
                                                                    : last;
  }
  template <typename ValueTy>
  constexpr const_iterator find_key_if(const_iterator first,
                                       const_iterator last,
                                       const ValueTy &value) const {
    return find_key_if_impl(map::lower_bound(value), last, value);
  }

  constexpr array_type ensure_unique_keys(const array_type &a) const {
    return constexpr_stuff::adjacent_find(
               a.begin(), a.end(), equal_to1st_pred<KeyComp>()) != a.end()
               ? throw "keys must be unique"
               : a;
  }
  template <typename Value, typename Comp>
  constexpr const_iterator lower_bound_impl(
      const_iterator first, const_iterator last, const Value &value,
      typename std::iterator_traits<const_iterator>::difference_type d,
      const Comp &comp) const {
    return d == 0
               ? first
               : comp((constexpr_stuff::next(first, d / 2)->first), value)
                     ? lower_bound_impl(constexpr_stuff::next(first, d / 2) + 1,
                                        last, value, d - ((d / 2) + 1), comp)
                     : lower_bound_impl(first, last, value, (d / 2), comp);
  }

public:
  constexpr map(const array_type &a) : values(ensure_unique_keys(msort(a))) {}
  constexpr ValueT lookup(KeyT k) const {
    return is_key_found(find_key_if(values.begin(), values.end(), k),
                        values.end())
        ->second;
  }
  constexpr ValueT operator[](KeyT k) const { return lookup(k); }
  constexpr KeyComp key_comp() const { return KeyComp(); }
  constexpr typename array_type::const_iterator
  lower_bound(const KeyT &key) const {
    return lower_bound_impl(
        values.begin(), values.end(), key,
        constexpr_stuff::distance(values.begin(), values.end()), key_comp());
  }
};
template <typename PairTy> using first_t = typename PairTy::first_type;
template <typename PairTy> using second_t = typename PairTy::second_type;
template <typename... PairsTy>
map<common_type_t<first_t<PairsTy>...>, common_type_t<second_t<PairsTy>...>,
    sizeof...(PairsTy)> constexpr make_map(PairsTy... pairs) {
  return map<common_type_t<first_t<PairsTy>...>,
             common_type_t<second_t<PairsTy>...>, sizeof...(pairs)>{
      {constexpr_stuff::forward<PairsTy>(pairs)...}};
}

template <typename FirstTy, typename SecondTy>
constexpr constexpr_stuff::pair<typename std::decay<FirstTy>::type,
                                typename std::decay<SecondTy>::type>
make_pair(FirstTy &&first, SecondTy &&second) {
  return constexpr_stuff::pair<typename std::decay<FirstTy>::type,
                               typename std::decay<SecondTy>::type>(
      constexpr_stuff::forward<FirstTy>(first),
      constexpr_stuff::forward<SecondTy>(second));
}
}

enum class CardSuit { Clubs, Diamonds, Hearts, Spades };

int main() {
  using namespace constexpr_stuff::udl;
  constexpr auto cardsuit_to_string_map = constexpr_stuff::make_map(
      constexpr_stuff::make_pair(CardSuit::Diamonds, "Diamonds"_sv),
      constexpr_stuff::make_pair(CardSuit::Spades, "Spades"_sv),
      constexpr_stuff::make_pair(CardSuit::Clubs, "Clubs"_sv),
      constexpr_stuff::make_pair(CardSuit::Hearts, "Hearts"_sv));

  constexpr auto string_to_cardsuit_map = constexpr_stuff::make_map(
      constexpr_stuff::make_pair("Diamonds"_sv, CardSuit::Diamonds),
      constexpr_stuff::make_pair("Spades"_sv, CardSuit::Spades),
      constexpr_stuff::make_pair("Clubs"_sv, CardSuit::Clubs),
      constexpr_stuff::make_pair("Hearts"_sv, CardSuit::Hearts));
  static_assert(cardsuit_to_string_map[string_to_cardsuit_map["Diamonds"_sv]] ==
                    "Diamonds"_sv,
                "cannot find element in the map");
  return 0;
}
