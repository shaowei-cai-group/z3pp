#include "nlsat/nlsat_clause.h"

// wzh
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
// hzw

namespace nlsat {
    // wzh
    typedef polynomial::manager::scoped_numeral scoped_numeral;
    typedef polynomial::manager::numeral_vector numeral_vector;
    // hzw

    // enum Variable_Ordering_Strategy_Type {NONE = 0, BROWN, TRIANGULAR, ONLYPOLY};
    // wzh
    enum Variable_Ordering_Strategy_Type {NONE = 0, BROWN, TRIANGULAR, ONLYPOLY, UNIVARIATE, FEATURE, ROOT};
    // hzw
    class VOS_Var_Info_Collector {
        struct imp;
        imp *  m_imp;
    public:
        VOS_Var_Info_Collector(pmanager & _pm, atom_vector const & atoms, unsigned _num_vars, unsigned _vos_type);
        ~VOS_Var_Info_Collector();
        void operator()(var_vector &perm);
        void collect(clause_vector const & cs);
    };
}