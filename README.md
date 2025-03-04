---
title: |
    CS 472: Provably Correct Programming\
    Final Project README
author: Himanshu Dongre
date: Spring 2024
header-includes:
    - \usepackage{fancyhdr}
    - \usepackage{graphicx}
    - \fancyhf{}
    - \lhead{\includegraphics[width=0.5in]{~/logos/uic.png}}
    - \renewcommand{\headrulewidth}{0pt}
    - \renewcommand{\footrulewidth}{0pt}
fancy_lists: true
---
\thispagestyle{fancy}

# Included files

+ `incsum.v`: The code file.
+ `README.pdf`: This README file.

# Important definitions and lemmas

## Lists:-

### List sum 

1. $\textcolor{purple}{\texttt{Fixpoint}}$ **`is_list`** `(l : list Z) (v : val) : iProp` $\Sigma$.

2. $\textcolor{purple}{\texttt{Fixpoint}}$ **`sum_list_coq`** `(l : list Z) : Z`.

3. $\textcolor{purple}{\texttt{Definition}}$ **`sum_list`** ` : val`.

4. ```haskell
Lemma sum_list_spec l v :
  {{{ is_list l v }}} sum_list v
  {{{ RET #(sum_list_coq l); is_list l v }}}.
  ```

### List increase

5. $\textcolor{purple}{\texttt{Definition}}$ **`inc_list`** ` : val`.

6. ```haskell
Lemma inc_list_spec n l v :
  {{{ is_list l v }}}
    inc_list #n v
  {{{ RET #(); is_list (map (Z.add n) l) v }}}.
  ```

## Spinlock:-

7. $\textcolor{purple}{\texttt{Definition}}$ **`is_lock`** `(lk : val) (R : iProp` $\Sigma$`) : iProp` $\Sigma$.\ 

### New lock

8. $\textcolor{purple}{\texttt{Definition}}$ **`newlock`** ` : val`.

9. ```haskell
Lemma newlock_spec R:
  {{{ R }}} newlock #() {{{ lk, RET lk; is_lock lk R }}}.
  ```

### Try lock

10. $\textcolor{purple}{\texttt{Definition}}$ **`try_lock`** ` : val`.

11. ```haskell
Lemma try_acquire_spec lk R :
  {{{ is_lock lk R }}} try_acquire lk
  {{{ b, RET #b; if b is true then R else True }}}.
  ```

### Acquire

12. $\textcolor{purple}{\texttt{Definition}}$ **`acquire`** ` : val`.

13. ```haskell
Lemma acquire_spec lk R :
  {{{ is_lock lk R }}} acquire lk {{{ RET #(); R }}}.
  ```

### Release

14. $\textcolor{purple}{\texttt{Definition}}$ **`release`** ` : val`.

15. ```haskell
Lemma release_spec lk R :
  {{{ is_lock lk R * R }}} release lk {{{ RET #(); True }}}.
  ```

### Invariant

16. $\textcolor{purple}{\texttt{Definition}}$ **`lock_inv`** `(l : loc) (R : iProp` $\Sigma$`) : iProp` $\Sigma$.

## Parallel inc sum:-

### Function

17. $\textcolor{purple}{\texttt{Definition}}$ **`parallel_inc_sum_locked`** `(lock : val) : val`.\
    One thread increases the given list by a given $n$. A second thread stores the list sum in a variable $sum$. Both threads acquire the same spinlock before executing their respective operation, and release it after. The function returns $sum$.

### Invariant

18. $\textcolor{purple}{\texttt{Definition}}$ **`inc_sum_inv`** `(n : Z) (l : list Z) (v : val) : iProp` $\Sigma$.\
    The function invariant states that there exists a list $l^\prime$ such that sum of $l$ is less than or equal to that of $l^\prime$, and separately, $v$ points to $l^\prime$.

### Helper lemma

19. ```haskell
Lemma sum_inc_eq_n_len : forall (l : list Z) n,
  (sum_list_coq (map (Z.add n) l) = (n * length l) + sum_list_coq l)%Z.
  ```

### Spec

20. $\textcolor{magenta}{\texttt{Theorem}}$ **`parallel_inc_sum_locked_spec`** `lock l v (n : Z)`.\
    Pre-condition : `is_lock lock` with resource `inc_sum_inv n l v`, and separately, $n \geq 0$.\
    Function call : `parallel_inc_sum_locked lock #n v`.\
    Post-condition: The function returns an integer $m$ such that the list sum of $l$ is less than or equal to $m$.

# References

+ All definitions and lemmas for "Lists" was taken from `ex_02_sumlist.v` distributed in the course.
+ All definitions and lemmas for "Spinlock" was taken from `ex_03_spinlock.v` distributed in the course.\
+ No external references used. 