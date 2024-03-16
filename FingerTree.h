#ifndef FINGERTREE_H
#define FINGERTREE_H

#include <cstddef>

namespace luke36 {

template <typename T> class FingerTree {
private:
  struct node;

  struct level;

  level *bottom;

  static void push_front_aux(level *, node *);

  static void push_back_aux(level *, node *);

  static node *front_aux(level *);

  static node *back_aux(level *);

  static void deepl(level *);

  static void deepr(level *);

  static node *pop_front_aux(level *);

  static node *pop_back_aux(level *);

  static level *append_aux(level *, node *[4], signed char, level *);

  static signed char lift_nodes(node *[12], signed char, node *[4]);

  static node *access_aux(level *, size_t, size_t *);

public:
  FingerTree();

  void push_front(const T &);

  void push_back(const T &);

  T &front();

  void pop_front();

  void pop_back();

  void append(FingerTree &);

  T &operator[](size_t);

  ~FingerTree();
};

template <typename T> struct FingerTree<T>::node {
  node(T *val) : val(val) {}
  node(signed char n) : nchild(n) {}
  std::size_t size;
  signed char nchild;
  node *child[3];
  T *val;
};

template <typename T> struct FingerTree<T>::level {
  level(signed char n1, signed char n2)
      : next(nullptr), root(nullptr), ndigitl(n1), ndigitr(n2) {}
  std::size_t size;
  level *next;
  node *root;
  node *digitl[4];
  signed char ndigitl;
  node *digitr[4];
  signed char ndigitr;
};

template <typename T> FingerTree<T>::FingerTree() : bottom(new level(0, 0)) {}

template <typename T> void FingerTree<T>::push_front_aux(level *l, node *n) {
  if (l->root != nullptr) {
    l->next = new level(0, 0);
    l->size = n->size + l->root->size;
    l->digitl[0] = n;
    l->digitr[0] = l->root;
    l->ndigitl = l->ndigitr = 1;
    l->root = nullptr;
  } else if (l->next == nullptr)
    l->root = n;
  else if (l->ndigitl == 4) {
    node *nn = new node(3);
    nn->child[0] = l->digitl[2];
    nn->child[1] = l->digitl[1];
    nn->child[2] = l->digitl[0];
    nn->size = l->digitl[0]->size + l->digitl[1]->size + l->digitl[2]->size;
    l->digitl[0] = l->digitl[3];
    l->digitl[1] = n;
    l->ndigitl = 2;
    l->size += n->size;
    push_front_aux(l->next, nn);
  } else {
    l->size += n->size;
    l->digitl[l->ndigitl++] = n;
  }
}

template <typename T> void FingerTree<T>::push_back_aux(level *l, node *n) {
  if (l->root != nullptr) {
    l->next = new level(0, 0);
    l->size = n->size + l->root->size;
    l->digitl[0] = l->root;
    l->digitr[0] = n;
    l->ndigitl = l->ndigitr = 1;
    l->root = nullptr;
  } else if (l->next == nullptr)
    l->root = n;
  else if (l->ndigitr == 4) {
    node *nn = new node(3);
    nn->child[0] = l->digitr[0];
    nn->child[1] = l->digitr[1];
    nn->child[2] = l->digitr[2];
    nn->size = l->digitr[0]->size + l->digitr[1]->size + l->digitr[2]->size;
    l->digitr[0] = l->digitr[3];
    l->digitr[1] = n;
    l->ndigitr = 2;
    l->size += n->size;
    push_back_aux(l->next, nn);
  } else {
    l->digitr[l->ndigitr++] = n;
    l->size += n->size;
  }
}

template <typename T> void FingerTree<T>::deepl(level *l) {
  if (l->next->next == nullptr && l->next->root == nullptr) {
    delete l->next;
    l->next = nullptr;
    signed char n = l->ndigitr;
    l->ndigitr = 0;
    node *temp[4];
    for (signed char i = 0; i < n; i++)
      temp[i] = l->digitr[i];
    for (signed char i = n - 1; i >= 0; i--)
      push_front_aux(l, temp[i]);
  } else {
    node *p = pop_front_aux(l->next);
    for (signed char i = p->nchild - 1; i >= 0; i--)
      l->digitl[l->ndigitl++] = p->child[i];
    delete p;
  }
}

template <typename T> void FingerTree<T>::deepr(level *l) {
  if (l->next->next == nullptr && l->next->root == nullptr) {
    delete l->next;
    l->next = nullptr;
    signed char n = l->ndigitl;
    l->ndigitl = 0;
    node *temp[4];
    for (signed char i = 0; i < n; i++)
      temp[i] = l->digitl[i];
    for (signed char i = 0; i < n; i++)
      push_front_aux(l, temp[i]);
  } else {
    node *p = pop_back_aux(l->next);
    for (signed char i = 0; i < p->nchild; i++)
      l->digitr[l->ndigitr++] = p->child[i];
    delete p;
  }
}

template <typename T>
typename FingerTree<T>::node *FingerTree<T>::pop_front_aux(level *l) {
  node *p = front_aux(l);
  if (l->root != nullptr)
    l->root = nullptr;
  else {
    l->size -= p->size;
    if ((--l->ndigitl) == 0)
      deepl(l);
  }
  return p;
}

template <typename T>
typename FingerTree<T>::node *FingerTree<T>::pop_back_aux(level *l) {
  node *p = back_aux(l);
  if (l->root != nullptr)
    l->root = nullptr;
  else {
    l->size -= p->size;
    if ((--l->ndigitr) == 0)
      deepr(l);
  }
  return p;
}

template <typename T>
typename FingerTree<T>::node *FingerTree<T>::front_aux(level *l) {
  if (l->root != nullptr)
    return l->root;
  else
    return l->digitl[l->ndigitl - 1];
}

template <typename T>
typename FingerTree<T>::node *FingerTree<T>::back_aux(level *l) {
  if (l->root != nullptr)
    return l->root;
  else
    return l->digitr[l->ndigitr - 1];
}

template <typename T>
typename FingerTree<T>::node *FingerTree<T>::access_aux(level *l, size_t pos,
                                                        size_t *start) {
  if (l->root != nullptr)
    return l->root;
  size_t accl = 0;
  size_t accr = l->size;
  for (signed char i = l->ndigitl - 1; i >= 0; i--) {
    accl += l->digitl[i]->size;
    if (accl > pos) {
      *start = accl - l->digitl[i]->size;
      return l->digitl[i];
    }
  }
  for (signed char i = l->ndigitr - 1; i >= 0; i--) {
    accr -= l->digitr[i]->size;
    if (accr <= pos) {
      *start = accr;
      return l->digitr[i];
    }
  }
  node *p = access_aux(l->next, pos - accl, start);
  accl += *start;
  for (signed char i = 0; i < p->nchild; i++) {
    accl += p->child[i]->size;
    if (accl > pos) {
      *start = accl - p->child[i]->size;
      return p->child[i];
    }
  }
}

template <typename T> void FingerTree<T>::push_front(const T &val) {
  T *p = new T(val);
  node *n = new node(p);
  n->size = 1;
  push_front_aux(bottom, n);
}

template <typename T> void FingerTree<T>::push_back(const T &val) {
  T *p = new T(val);
  node *n = new node(p);
  n->size = 1;
  push_back_aux(bottom, n);
}

template <typename T> void FingerTree<T>::pop_front() {
  node *p = pop_front_aux(bottom);
  delete p->val;
  delete p;
}

template <typename T> void FingerTree<T>::pop_back() {
  node *p = pop_back_aux(bottom);
  delete p->val;
  delete p;
}

template <typename T> FingerTree<T>::~FingerTree() {
  while (!(bottom->next == nullptr && bottom->root == nullptr))
    pop_front();
  delete bottom;
}

template <typename T> T &FingerTree<T>::front() {
  return *(front_aux(bottom)->val);
}

template <typename T>
signed char FingerTree<T>::lift_nodes(node *nodes[12], signed char nnodes,
                                      node *newdigit[4]) {
  signed char s = 0;
  signed char p = 0;
  while (1) {
    if (nnodes - s == 2) {
      newdigit[p++] = new node(2);
      newdigit[p - 1]->child[0] = nodes[s];
      newdigit[p - 1]->child[1] = nodes[s + 1];
      newdigit[p - 1]->size = nodes[s]->size + nodes[s + 1]->size;
      break;
    } else if (nnodes - s == 3) {
      newdigit[p++] = new node(3);
      newdigit[p - 1]->child[0] = nodes[s];
      newdigit[p - 1]->child[1] = nodes[s + 1];
      newdigit[p - 1]->child[2] = nodes[s + 2];
      newdigit[p - 1]->size =
          nodes[s]->size + nodes[s + 1]->size + nodes[s + 2]->size;
      break;
    } else if (nnodes - s == 4) {
      newdigit[p++] = new node(2);
      newdigit[p - 1]->child[0] = nodes[s];
      newdigit[p - 1]->child[1] = nodes[s + 1];
      newdigit[p - 1]->size = nodes[s]->size + nodes[s + 1]->size;
      newdigit[p++] = new node(2);
      newdigit[p - 1]->child[0] = nodes[s + 2];
      newdigit[p - 1]->child[1] = nodes[s + 3];
      newdigit[p - 1]->size = nodes[s + 2]->size + nodes[s + 3]->size;
      break;
    } else {
      newdigit[p++] = new node(3);
      newdigit[p - 1]->child[0] = nodes[s];
      newdigit[p - 1]->child[1] = nodes[s + 1];
      newdigit[p - 1]->child[2] = nodes[s + 2];
      newdigit[p - 1]->size =
          nodes[s]->size + nodes[s + 1]->size + nodes[s + 2]->size;
      s += 3;
    }
  }
  return p;
}

template <typename T>
typename FingerTree<T>::level *
FingerTree<T>::append_aux(level *l1, node *digit[4], signed char ndigit,
                          level *l2) {
  if (l1->next == nullptr) {
    for (signed char i = ndigit - 1; i >= 0; i--)
      push_front_aux(l2, digit[i]);
    if (l1->root != nullptr)
      push_front_aux(l2, l1->root);
    delete l1;
    return l2;
  } else if (l2->next == nullptr) {
    for (signed char i = 0; i < ndigit; i++)
      push_back_aux(l1, digit[i]);
    if (l2->root != nullptr)
      push_back_aux(l1, l2->root);
    delete l2;
    return l1;
  } else {
    for (signed char i = 0; i < ndigit; i++)
      l1->size += digit[i]->size;
    l1->size += l2->size;
    node *nodes[12];
    node *newdigit[4];
    signed char e = 0;
    for (signed char i = 0; i < l1->ndigitr; i++)
      nodes[e++] = l1->digitr[i];
    for (signed char i = 0; i < ndigit; i++)
      nodes[e++] = digit[i];
    for (signed char i = l2->ndigitl - 1; i >= 0; i--)
      nodes[e++] = l2->digitl[i];
    signed char nnew = lift_nodes(nodes, e, newdigit);
    level *chosen = append_aux(l1->next, newdigit, nnew, l2->next);
    for (signed char i = 0; i < l2->ndigitr; i++)
      l1->digitr[i] = l2->digitr[i];
    l1->ndigitr = l2->ndigitr;
    delete l2;
    l1->next = chosen;
    return l1;
  }
}

template <typename T> void FingerTree<T>::append(FingerTree<T> &other) {
  if (other.bottom->next == nullptr && other.bottom->root == nullptr)
    return;
  else {
    node *temp[4];
    temp[0] = pop_front_aux(other.bottom);
    level *newbott = append_aux(bottom, temp, 1, other.bottom);
    if (newbott != bottom) {
      bottom = newbott;
      other.bottom->next = nullptr;
      other.bottom->root = nullptr;
    } else
      other.bottom = new level(0, 0);
  }
}

template <typename T> T &FingerTree<T>::operator[](size_t pos) {
  size_t temp;
  node *p = access_aux(bottom, pos, &temp);
  return *(p->val);
}

} // namespace luke36

#endif
