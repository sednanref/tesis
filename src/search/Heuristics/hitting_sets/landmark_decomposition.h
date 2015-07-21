#ifndef LANDMARK_DECOMPOSITION_H
#define LANDMARK_DECOMPOSITION_H

#include "landmark.h"

#include <iostream>
#include <vector>
#include <set>

namespace HittingSets {

struct LandmarkDecomposition {
    const Relaxed::Problem &rproblem_;
    int num_operators_;
    bool optimal_;

    std::vector<std::pair<int, const Landmark*> > F_;
    std::set<int> roots_;
    int width_;
    
    std::vector<Relaxed::OperatorSet> hitting_sets_;
    Relaxed::OperatorSet *global_hitting_set_;

    std::vector<int> hitting_set_costs_;
    int global_hitting_set_cost_;

    std::vector<int> rank_;
    mutable std::vector<int> parent_;

    LandmarkDecomposition(const Relaxed::Problem &rproblem, bool optimal = true);
    ~LandmarkDecomposition();

    void initialize();
    void clear_hitting_sets();
    void prepare_computation();
    void remove_landmarks();

    void Union(int i, int j);
    int Find(int i) const;
    int Add(const Landmark *L);
    int Width(const Relaxed::OperatorSet &cutset);
    void Repartition_bucket(int bucket, bool solve);

    bool is_hitting_set(const Relaxed::OperatorSet &hitting_set) const;

    enum { DEFAULT = 0, OPTIMAL = 1, SUBOPTIMAL = 2 };
    int solve(int type = DEFAULT);
    void solve_bucket(int bucket, int type = DEFAULT);

    void dump_partition(std::ostream &os) const;
    void dump_landmarks(std::ostream &os, int indent) const;
    void dump_landmarks_in_bucket(std::ostream &os, int indent, int bucket) const;

};

} // end of namespace

#endif

