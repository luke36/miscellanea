#include <cstdio>

typedef long long Data;

namespace wbt {

struct Node;

typedef Node *NodePtr;

struct Node {
  int refcnt;
  int size;
  NodePtr left;
  Data data;
  NodePtr right;
  Node(NodePtr left, Data data, NodePtr right);
  Node(NodePtr left, Data data, NodePtr right, int size);
};

inline int size(NodePtr t) {
  if (t) {
    return t->size;
  } else {
    return 0;
  }
}

inline void incref(NodePtr a) {
  if (a != nullptr)
    a->refcnt += 1;
}

inline void decref(NodePtr a) {
  if (a != nullptr)
    a->refcnt -= 1;
}

inline Node::Node(NodePtr left, Data data, NodePtr right)
  : left(left), data(data), right(right), refcnt(0) {
  incref(left);
  incref(right);
  size = 1 + wbt::size(left) + wbt::size(right);
}

inline Node::Node(NodePtr left, Data data, NodePtr right, int size)
: left(left), data(data), right(right), refcnt(0), size(size) {
  incref(left);
  incref(right);
}

inline NodePtr singleLeft(NodePtr a) {
  NodePtr
    b = a->right,
    x = a->left,
    y = b->left,
    z = b->right;
  if (a->refcnt == 0 && b->refcnt == 1) {
    b->size = a->size;
    a->size -= size(z) + 1;
    a->right = y;
    b->left = a;
    a->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (a->refcnt == 0) {
    int all_size = a->size;
    a->size -= size(z) + 1;
    a->right = y;
    incref(y);
    decref(b);
    return new Node(a, b->data, z, all_size);
  } else {
    return new Node(new Node(x, a->data, y, a->size - size(z) - 1),
                    b->data,
                    z,
                    a->size);
  }
}

inline NodePtr singleRight(NodePtr b) {
  NodePtr
    a = b->left,
    x = a->left,
    y = a->right,
    z = b->right;
  if (b->refcnt == 0 && a->refcnt == 1) {
    a->size = b->size;
    b->size -= size(x) + 1;
    b->left = y;
    a->right = b;
    b->refcnt = 1;
    a->refcnt = 0;
    return a;
  } else if (b->refcnt == 0) {
    int all_size = b->size;
    b->size -= size(x) + 1;
    b->left = y;
    incref(y);
    decref(a);
    return new Node(x, a->data, b, all_size);
  } else {
    return new Node(x,
                    a->data,
                    new Node(y, b->data, z, b->size - size(x) - 1),
                    b->size);
  }
}

inline NodePtr doubleLeft(NodePtr a) {
  NodePtr
    x = a->left,
    c = a->right,
    b = c->left,
    y = b->left,
    z = b->right,
    w = c->right;
  if (a->refcnt == 0 && c->refcnt == 1 && b->refcnt == 1) {
    int y_size = size(y);
    b->size = a->size;
    a->size += - c->size + y_size;
    c->size -= y_size + 1;
    a->right = y;
    c->left = z;
    b->left = a;
    b->right = c;
    a->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (a->refcnt == 0 && c->refcnt == 1) {
    int
      all_size = a->size,
      y_size = size(y);
    a->size += - c->size + y_size;
    c->size -= y_size + 1;
    a->right = y;
    c->left = z;
    c->refcnt = 0;
    incref(y);
    incref(z);
    decref(b);
    return new Node(a, b->data, c, all_size);
  } else if (a->refcnt == 0) {
    int
      all_size = a->size,
      y_size = size(y);
    a->size += - c->size + y_size;
    a->right = y;
    incref(y);
    decref(c);
    return new Node(a,
                    b->data,
                    new Node(z, c->data, w, c->size - y_size - 1),
                    all_size);
  } else {
    int y_size = size(y);
    return new Node(new Node(x, a->data, y, a->size - c->size + y_size),
                    b->data,
                    new Node(z, c->data, w, c->size - y_size - 1),
                    a->size);
  }
}

inline NodePtr doubleRight(NodePtr c) {
  NodePtr
    a = c->left,
    x = a->left,
    b = a->right,
    y = b->left,
    z = b->right,
    w = c->right;
  if (c->refcnt == 0 && a->refcnt == 1 && b->refcnt == 1) {
    int z_size = size(z);
    b->size = c->size;
    c->size += - a->size + z_size;
    a->size -= z_size + 1;
    c->left = z;
    a->right = y;
    b->left = a;
    b->right = c;
    c->refcnt = 1;
    b->refcnt = 0;
    return b;
  } else if (c->refcnt == 0 && a->refcnt == 1) {
    int
      all_size = c->size,
      z_size = size(z);
    c->size += - a->size + z_size;
    a->size -= z_size + 1;
    a->right = y;
    c->left = z;
    a->refcnt = 0;
    incref(y);
    incref(z);
    decref(b);
    return new Node(a, b->data, c, all_size);
  } else if (c->refcnt == 0) {
    int
      all_size = c->size,
      z_size = size(z);
    c->size += - a->size + z_size;
    c->left = z;
    incref(z);
    decref(a);
    return new Node(new Node(x, a->data, y, a->size - z_size - 1),
                    b->data,
                    c,
                    all_size);
  } else {
    int z_size = size(z);
    return new Node(new Node(x, a->data, y, a->size - z_size - 1),
                    b->data,
                    new Node(z, c->data, w, c->size - a->size + z_size),
                    c->size);
  }
}

// a < b
inline bool isBalanced(NodePtr a, NodePtr b) {
  return 5 * (size(a) + 1) >= 2 * (size(b) + 1);
}

inline bool isSingle(NodePtr a, NodePtr b) {
  return 2 * (size(a) + 1) < 3 * (size(b) + 1);
}

// t->left < t->right
inline NodePtr balanceLeft(NodePtr t) {
  if (isBalanced(t->left, t->right)) {
    return t;
  } else if (isSingle(t->right->left, t->right->right)) {
    return singleLeft(t);
  } else {
    return doubleLeft(t);
  }
}

// t->left > t->right
inline NodePtr balanceRight(NodePtr t) {
  if (isBalanced(t->right, t->left)) {
    return t;
  } else if (isSingle(t->left->right, t->left->left)) {
    return singleRight(t);
  } else {
    return doubleRight(t);
  }
}

static NodePtr insert(Data v, NodePtr t) {
  if (t == nullptr) {
    return new Node(nullptr, v, nullptr, 1);
  } else if (v < t->data) {
    if (t->refcnt == 0) {
      decref(t->left);
      t->left = insert(v, t->left);
      t->size = 1 + size(t->left) + size(t->right);
      t->left->refcnt += 1;
      return balanceRight(t);
    } else {
      return balanceRight(new Node(insert(v, t->left),
                                   t->data,
                                   t->right));
    }
  } else if (v > t->data) {
    if (t->refcnt == 0) {
      decref(t->right);
      t->right = insert(v, t->right);
      t->size = 1 + size(t->left) + size(t->right);
      t->right->refcnt += 1;
      return balanceLeft(t);
    } else {
      return balanceLeft(new Node(t->left,
                                  t->data,
                                  insert(v, t->right)));
    }
  } else {
    return t;
  }
}

static NodePtr removeMin(NodePtr t, Data &v) {
  if (t->refcnt == 0) {
    if (t->left == nullptr) {
      v = t->data;
      NodePtr ret = t->right;
      delete t;
      decref(ret);
      return ret;
    } else {
      t->size -= 1;
      t->left->refcnt -= 1;
      t->left = removeMin(t->left, v);
      incref(t->left);
      return balanceLeft(t);
    }
  } else {
    if (t->left == nullptr) {
      v = t->data;
      return t->right;
    } else {
      return balanceLeft(new Node(removeMin(t->left, v),
                                  t->data,
                                  t->right,
                                  t->size - 1));
    }
  }
}

static NodePtr remove(Data v, NodePtr t) {
  if (t == nullptr) {
    return nullptr;
  } else if (v < t->data) {
    if (t->refcnt == 0) {
      decref(t->left);
      t->left = remove(v, t->left);
      t->size = 1 + size(t->left) + size(t->right);
      incref(t->left);
      return balanceLeft(t);
    } else {
      return balanceLeft(new Node(remove(v, t->left),
                                  t->data,
                                  t->right));
    }
  } else if (v > t->data) {
    if (t->refcnt == 0) {
      decref(t->right);
      t->right = remove(v, t->right);
      t->size = 1 + size(t->left) + size(t->right);
      incref(t->right);
      return balanceRight(t);
    } else {
      return balanceRight(new Node(t->left,
                                   t->data,
                                   remove(v, t->right)));
    }
  } else {
    if (t->refcnt == 0) {
      if (t->left == nullptr) {
        NodePtr ret = t->right;
        delete t;
        decref(ret);
        return ret;
      } else if (t->right == nullptr) {
        NodePtr ret = t->left;
        delete t;
        decref(ret);
        return ret;
      } else {
        t->right->refcnt -= 1;
        t->right = removeMin(t->right, t->data);
        t->size -= 1;
        incref(t->right);
        return balanceRight(t);
      }
    } else {
      if (t->left == nullptr) {
        return t->right;
      } else if (t->right == nullptr) {
        return t->left;
      } else {
        Data min(-1);
        NodePtr r = removeMin(t->right, min);
        return balanceRight(new Node(t->left,
                                     min,
                                     r,
                                     t->size - 1));
      }
    }
  }
}

static Data at(int p, NodePtr t) {
  int sz = size(t->left);
  if (sz == p) {
    return t->data;
  } else if (sz < p) {
    return at(p - sz - 1, t->right);
  } else {
    return at(p, t->left);
  }
}

static int nlt(Data v, NodePtr t) {
  if (t == nullptr) {
    return 0;
  } else if (t->data >= v) {
    return nlt(v, t->left);
  } else {
    return 1 + size(t->left) + nlt(v, t->right);
  }
}

static int ngt(Data v, NodePtr t) {
  if (t == nullptr) {
    return 0;
  } else if (t->data <= v) {
    return ngt(v, t->right);
  } else {
    return 1 + size(t->right) + ngt(v, t->left);
  }
}

inline int nbetween(Data a, Data b, NodePtr t) {
  return size(t) - nlt(a, t) - ngt(b, t);
}

static bool member(Data v, NodePtr t) {
  if (t == nullptr) {
    return false;
  } else if (v < t->data) {
    return member(v, t->left);
  } else if (v > t->data) {
    return member(v, t->right);
  } else {
    return true;
  }
}

void printTree(NodePtr t) {
  if (t != nullptr) {
    fprintf(stderr, "(");
    printTree(t->left);
    fprintf(stderr, " %lld [%d] ", t->data, t->refcnt);
    printTree(t->right);
    fprintf(stderr, ")");
  }
}

static void freeTree(NodePtr t) {
  if (t != nullptr) {
    if (t->refcnt == 0) {
      decref(t->left);
      decref(t->right);
      freeTree(t->left);
      freeTree(t->right);
      delete t;
    }
  }
}

}

class ESet {
private:
  wbt::NodePtr root;
public:
  ESet() : root(nullptr) {}
  ESet(const ESet &other) : root(other.root) {
    wbt::incref(root);
  }
  ~ESet() {
    wbt::decref(root);
    wbt::freeTree(root);
}

  ESet &operator=(const ESet &other) {
    wbt::decref(root);
    root = other.root;
    wbt::incref(root);
    return *this;
  }

  void insert(Data v) {
    wbt::decref(root);
    root = wbt::insert(v, root);
    wbt::incref(root);
  }

  void erase(Data v) {
    wbt::decref(root);
    root = wbt::remove(v, root);
    wbt::incref(root);
  }

  int size() const {
    return wbt::size(root);
  }

  bool empty() const {
    return root == nullptr;
  }

  int countBetween(Data a, Data b) const {
    return wbt::nbetween(a, b, root);
  }

  bool has(Data v) const {
    return wbt::member(v, root);
  }

  Data at(int pos) const {
    return wbt::at(pos, root);
  }

  Data operator[](int pos) const {
    return at(pos);
  }

  class iterator {
    friend class ESet;
  private:
    ESet *iteratee;
    int index;
    iterator(ESet *iteratee, int index) : iteratee(iteratee), index(index) {}
  public:
    iterator &operator=(const iterator &other) = default;
    
    iterator &operator+=(const int &n) {
      index += n;
      return *this;
    }

    iterator &operator-=(const int &n) {
      return (*this += (-n));
    }

    iterator operator+(const int &n) const {
      iterator tmp = *this;
      return tmp += n;
    }

    iterator operator-(const int &n) const {
      return (*this + (-n));
    }

    iterator operator++(int) {
      iterator tmp = *this;
      *this += 1;
      return tmp;
    }

    iterator operator--(int) {
      iterator tmp = *this;
      *this -= 1;
      return tmp;
    }

    iterator &operator++() {
      return *this += 1;
    }

    iterator &operator--() {
      return *this -= 1;
    }

    Data operator*() const {
      return iteratee->at(index);
    }

    bool operator==(const iterator &other) const {
      return iteratee == other.iteratee && index == other.index;
    }

    bool operator!=(const iterator &other) const {
      return !(*this == other);
    }
  };

  friend class iterator;

  iterator begin() {
    return iterator(this, 0);
  }

  iterator end() {
    return iterator(this, size());
  }

  void show() const {
    wbt::printTree(root);
    fprintf(stderr, "\n");
  }
};

#include "io.h"
#include <vector>
#include <iostream>
#include <chrono>

using namespace std;

int main() {
  auto begin = std::chrono::high_resolution_clock::now();
  vector<ESet> sets = { ESet() };

  enum op o;
  int i = 0;
  long long rand1 = 0;
  long long rand2 = 0;
  int t = 0;

  while (read(o, i, rand1, rand2) != -1) {
    switch (o) {
    case INS:
      sets[i].insert(rand1);
      break;
    case DEL:
      sets[i].erase(rand1);
      break;
    case ASK:
      write(sets[i].has(rand1));
      break;
    case FRK:
      sets.emplace_back(sets[i]);
      break;
    case RAN:
      write(sets[i].countBetween(rand1, rand2));
      break;
    case PRE:
    case SUC:
      break;
    }
  }

  auto end = std::chrono::high_resolution_clock::now();
  std::cerr << std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin)
                   .count()
            << std::endl;
}
