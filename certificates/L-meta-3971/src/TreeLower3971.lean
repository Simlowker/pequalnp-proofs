import TreeConclusion3971
import RecordFacts3971
import Joined397111
import Joined397112
import Joined397113
import Joined397114
import Joined397122
import Joined397123
import BoxRange3971
namespace PetersenNegated3971
theorem tree_lower (o t : Formula) (once : marked o=1)
    (fit : ∀ r : Fin 512, o.eval (outerValue t r.val)=edge r.val) :
    14<o.leaves-1+t.leaves :=
  tree_from_checks all_records (classify_joins joined11 joined12 joined13 joined14 joined22 joined23) all_boxes o t once fit
#print axioms tree_lower
end PetersenNegated3971
