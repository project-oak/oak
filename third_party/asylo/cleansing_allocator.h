/*
 *
 * Copyright 2017 Asylo authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

#ifndef ASYLO_UTIL_CLEANSING_ALLOCATOR_H_
#define ASYLO_UTIL_CLEANSING_ALLOCATOR_H_

#include <openssl/mem.h>
#include <cstdlib>
#include <limits>
#include <memory>
#include <type_traits>

namespace asylo {

/// CleansingAllocator is a minimal C++11
/// [allocator](http://en.cppreference.com/w/cpp/concept/Allocator) that
/// guarantees memory cleansing before freeing the memory. Dynamic storage
/// elements such as `std::vector` or `std::basic_string`, when backed by this
/// allocator, provide convenient storage for cryptographic secrets.
//
/// CleansingAllocator layers on top of another C++ allocator that is provided
/// as a template parameter, and exposes most of the functionality of the
/// underlying allocator in a passthrough fashion. It however cleanses the
/// memory being deallocated before passing it to the deallocate method of
/// the underlying allocator.
template <typename T, class A = std::allocator<T>>
class CleansingAllocator {
 public:
  using value_type = typename std::allocator_traits<A>::value_type;
  using pointer = typename std::allocator_traits<A>::pointer;
  using const_pointer = typename std::allocator_traits<A>::const_pointer;

  // reference and const_reference are non-standard extensions that are used
  // by some containers in the standard library. Template parameter |A| must
  // provide these extensions if the library implementation relies on these
  // extensions.
  using reference = typename A::reference;
  using const_reference = typename A::const_reference;

  using size_type = typename std::allocator_traits<A>::size_type;
  using difference_type = typename std::allocator_traits<A>::difference_type;

  CleansingAllocator(const A &alloc = A()) : alloc_{alloc} {};
  template <typename U, class B>
  explicit CleansingAllocator(const CleansingAllocator<U, B> &a)
      : alloc_{a.alloc_} {}
  ~CleansingAllocator() = default;

  template <typename U>
  struct rebind {
    using other = CleansingAllocator<
        U, typename std::allocator_traits<A>::template rebind_alloc<U>>;
  };

  pointer address(T &r) {
    return std::allocator_traits<A>::address(alloc_, r);
  }
  const_pointer address(const T &r) {
    return std::allocator_traits<A>::address(alloc_, r);
  }

  pointer allocate(size_type n) {
    return std::allocator_traits<A>::allocate(alloc_, n);
  }

  void deallocate(pointer ptr, size_type n) {
    OPENSSL_cleanse(ptr, n * sizeof(T));
    std::allocator_traits<A>::deallocate(alloc_, ptr, n);
  }

  std::size_t max_size() const {
    return std::allocator_traits<A>::max_size(alloc_);
  }

  void construct(T *ptr, const T &t) {
    std::allocator_traits<A>::construct(alloc_, ptr, t);
  }
  void destroy(T *ptr) { std::allocator_traits<A>::destroy(alloc_, ptr); }

  // Declare all instantiations of CleansingAllocator to be friends to make the
  // cross-specialization copy constructor work.
  template <typename U, class B>
  friend class CleansingAllocator;

  // Equality operators that compare arbitrary specializations of this
  // template class need to access the member alloc_.
  template <typename U, typename V, class B, class C>
  friend bool operator==(const CleansingAllocator<U, B> &lhs,
                         const CleansingAllocator<V, C> &rhs);

 private:
  A alloc_;
};

template <typename T, typename U, class A, class B>
bool operator==(const CleansingAllocator<T, A> &lhs,
                const CleansingAllocator<U, B> &rhs) {
  return lhs.alloc_ == rhs.alloc_;
}

template <typename T, typename U, class A, class B>
bool operator!=(const CleansingAllocator<T, A> &lhs,
                const CleansingAllocator<U, B> &rhs) {
  return !(lhs == rhs);
}

}  // namespace asylo
#endif  // ASYLO_UTIL_CLEANSING_ALLOCATOR_H_
