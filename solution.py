import bisect
from Planner import TablePlan, SelectPlan, ProjectPlan, ProductPlan
from Record import TableScan, RecordID
from RelationalOp import Predicate, Constant, Expression

# =============================================================
# Helpers
# =============================================================

def _get_field(expression):
    v = expression.exp_value
    if isinstance(v, str):
        return v
    return None

def _extract_eq_constant(term):
    lf = _get_field(term.lhs)
    rf = _get_field(term.rhs)
    lv = term.lhs.exp_value
    rv = term.rhs.exp_value
    if lf is not None and isinstance(rv, Constant):
        return lf, rv.const_value
    if rf is not None and isinstance(lv, Constant):
        return rf, lv.const_value
    return None

def _extract_eq_fields(term):
    lf = _get_field(term.lhs)
    rf = _get_field(term.rhs)
    if lf is not None and rf is not None:
        return lf, rf
    return None

def _term_fields(term):
    fields = set()
    for expr in (term.lhs, term.rhs):
        name = _get_field(expr)
        if name is not None:
            fields.add(name)
    return fields

def _table_fields(plan):
    return set(plan.plan_schema().field_info.keys())

# =============================================================
# BTreeIndex & CompositeIndex
# =============================================================

class BTreeIndex:
    def __init__(self, tx, index_name, key_type, key_length):
        self.data = []

    def insert(self, key_value, record_id):
        bisect.insort(self.data, (key_value, record_id.blk_num, record_id.slot_num))

    def search(self, key_value):
        i = bisect.bisect_left(self.data, (key_value, -1, -1))
        result = []
        while i < len(self.data) and self.data[i][0] == key_value:
            _, b, s = self.data[i]
            result.append(RecordID(b, s))
            i += 1
        return result

    def close(self):
        pass


class CompositeIndex:
    def __init__(self, tx, index_name, field_names, field_types, field_lengths):
        self.data = []

    def insert(self, field_values, record_id):
        key = tuple(field_values)
        bisect.insort(self.data, (key, record_id.blk_num, record_id.slot_num))

    def search(self, field_values):
        key = tuple(field_values)
        i = bisect.bisect_left(self.data, (key, -1, -1))
        result = []
        while i < len(self.data) and self.data[i][0] == key:
            _, b, s = self.data[i]
            result.append(RecordID(b, s))
            i += 1
        return result

    def close(self):
        pass

# =============================================================
# IndexScan
# =============================================================

class IndexScan:
    def __init__(self, table_scan, index, search_key):
        self.ts = table_scan
        self.rids = index.search(search_key)
        self.pos = -1

    def beforeFirst(self):
        self.pos = -1

    def nextRecord(self):
        self.pos += 1
        if self.pos >= len(self.rids):
            return False
        self.ts.moveToRecordID(self.rids[self.pos])
        return True

    def getInt(self, f): return self.ts.getInt(f)
    def getString(self, f): return self.ts.getString(f)
    def getVal(self, f): return self.ts.getVal(f)
    def hasField(self, f): return self.ts.hasField(f)
    def closeRecordPage(self): self.ts.closeRecordPage()


class _IndexPlan:
    def __init__(self, tx, table_name, layout, index, search_key):
        self.tx = tx
        self.table_name = table_name
        self.layout = layout
        self.index = index
        self.search_key = search_key

    def open(self):
        ts = TableScan(self.tx, self.table_name, self.layout)
        return IndexScan(ts, self.index, self.search_key)

    def blocksAccessed(self): return max(1, self.recordsOutput() // 10)
    def recordsOutput(self):
        actual = len(self.index.search(self.search_key))
        return actual if actual > 0 else 1
    def distinctValues(self, f): return 1
    def plan_schema(self): return self.layout.schema

# =============================================================
# IndexNestedLoopScan & Plan
# =============================================================

class IndexNestedLoopScan:
    def __init__(self, outer_scan, inner_ts, inner_index,
                 outer_join_field, inner_join_field):
        self.outer = outer_scan
        self.inner_ts = inner_ts
        self.inner_index = inner_index
        self.outer_field = outer_join_field
        self.inner_field = inner_join_field
        self._inner_rids = []
        self._inner_pos = -1
        self._exhausted = False
        self._advance_outer()

    def _advance_outer(self):
        while True:
            if not self.outer.nextRecord():
                self._inner_rids = []
                self._inner_pos = -1
                self._exhausted = True
                return
            key = self.outer.getVal(self.outer_field)
            if hasattr(key, 'const_value'):
                key = key.const_value
            self._inner_rids = self.inner_index.search(key)
            self._inner_pos = -1
            if self._inner_rids:
                self._exhausted = False
                return

    def beforeFirst(self):
        if hasattr(self.outer, 'beforeFirst'):
            self.outer.beforeFirst()
        self._advance_outer()

    def nextRecord(self):
        if self._exhausted:
            return False
        self._inner_pos += 1
        if self._inner_pos < len(self._inner_rids):
            self.inner_ts.moveToRecordID(self._inner_rids[self._inner_pos])
            return True
        self._advance_outer()
        if self._exhausted:
            return False
        self._inner_pos = 0
        self.inner_ts.moveToRecordID(self._inner_rids[0])
        return True

    def getVal(self, f):
        if self.inner_ts.hasField(f):
            return self.inner_ts.getVal(f)
        return self.outer.getVal(f)

    def getInt(self, f):
        v = self.getVal(f)
        return v.const_value if hasattr(v, 'const_value') else v

    def getString(self, f):
        v = self.getVal(f)
        return v.const_value if hasattr(v, 'const_value') else v

    def hasField(self, f):
        return self.inner_ts.hasField(f) or self.outer.hasField(f)

    def closeRecordPage(self):
        self.inner_ts.closeRecordPage()
        if hasattr(self.outer, 'closeRecordPage'):
            self.outer.closeRecordPage()


class IndexNestedLoopPlan:
    def __init__(self, tx, outer_plan, inner_table, inner_layout,
                 inner_index, outer_field, inner_field):
        self.tx = tx
        self.outer_plan = outer_plan
        self.inner_table = inner_table
        self.inner_layout = inner_layout
        self.inner_index = inner_index
        self.outer_field = outer_field
        self.inner_field = inner_field
        import copy
        self._schema = copy.deepcopy(outer_plan.plan_schema())
        for fname, finfo in inner_layout.schema.field_info.items():
            if fname not in self._schema.field_info:
                self._schema.field_info[fname] = finfo

    def open(self):
        outer_scan = self.outer_plan.open()
        inner_ts = TableScan(self.tx, self.inner_table, self.inner_layout)
        return IndexNestedLoopScan(
            outer_scan, inner_ts, self.inner_index,
            self.outer_field, self.inner_field
        )

    def blocksAccessed(self):
        return self.outer_plan.blocksAccessed() + (self.outer_plan.recordsOutput() or 1)

    def recordsOutput(self):
        return self.outer_plan.recordsOutput() or 1

    def distinctValues(self, f): return 1
    def plan_schema(self): return self._schema

# =============================================================
# BetterQueryPlanner
# =============================================================

class BetterQueryPlanner:
    def __init__(self, mm, indexes=None):
        self.mm = mm
        self.indexes = indexes or {}

    def createPlan(self, tx, query_data, plan_overrides=None, indexes=None):
        active_indexes = indexes if indexes is not None else self.indexes
        tables = list(query_data['tables'])
        fields = query_data['fields']
        predicate = query_data.get('predicate')
        terms = list(predicate.terms) if predicate else []

        table_plans = {}
        for t in tables:
            if plan_overrides and t in plan_overrides:
                table_plans[t] = plan_overrides[t]
            else:
                table_plans[t] = TablePlan(tx, t, self.mm)

        single_terms = {t: [] for t in tables}
        join_terms = []
        for term in terms:
            tf = _term_fields(term)
            matched = [t for t in tables if tf.issubset(_table_fields(table_plans[t]))]
            if len(matched) == 1:
                single_terms[matched[0]].append(term)
            else:
                join_terms.append(term)

        plans = {}
        for t in tables:
            p = table_plans[t]
            if single_terms[t]:
                pred = Predicate()
                pred.terms = single_terms[t]
                p = SelectPlan(p, pred)
            plans[t] = p

        remaining = set(tables)
        start_table = min(remaining, key=lambda t: plans[t].recordsOutput() or 1)
        remaining.remove(start_table)

        current_plan = plans[start_table]
        current_fields = _table_fields(table_plans[start_table])

        while remaining:
            best_table = None
            best_score = float('inf')
            for t in remaining:
                score = plans[t].recordsOutput() or 1
                t_fields = _table_fields(table_plans[t])
                has_connection = any(
                    (_term_fields(term) & current_fields) and (_term_fields(term) & t_fields)
                    for term in join_terms
                )
                if has_connection:
                    score *= 0.01
                if score < best_score:
                    best_score = score
                    best_table = t

            remaining.remove(best_table)

            inl_plan = self._try_index_nl_join(
                tx, current_plan, current_fields, best_table, join_terms, active_indexes
            )

            if inl_plan is not None:
                current_plan = inl_plan
                applicable = [
                    term for term in join_terms
                    if _term_fields(term).issubset(
                        current_fields | _table_fields(table_plans[best_table])
                    )
                ]
                for term in applicable:
                    if term in join_terms:
                        join_terms.remove(term)
            else:
                current_plan = ProductPlan(current_plan, plans[best_table])
                applicable = [
                    term for term in join_terms
                    if _term_fields(term).issubset(
                        current_fields | _table_fields(table_plans[best_table])
                    )
                ]
                if applicable:
                    pred = Predicate()
                    pred.terms = applicable
                    current_plan = SelectPlan(current_plan, pred)
                    for term in applicable:
                        join_terms.remove(term)

            current_fields |= _table_fields(table_plans[best_table])

        return ProjectPlan(current_plan, *fields)

    def _try_index_nl_join(self, tx, outer_plan, outer_fields,
                           inner_table, join_terms, indexes):
        inner_indexes = indexes.get(inner_table, {})
        if not inner_indexes:
            return None

        inner_layout = self.mm.getLayout(tx, inner_table)
        inner_schema_fields = set(inner_layout.schema.field_info.keys())

        for term in join_terms:
            pair = _extract_eq_fields(term)
            if pair is None:
                continue
            lf, rf = pair

            outer_field, inner_field = None, None
            if lf in outer_fields and rf in inner_schema_fields:
                outer_field, inner_field = lf, rf
            elif rf in outer_fields and lf in inner_schema_fields:
                outer_field, inner_field = rf, lf

            if outer_field is None:
                continue

            if inner_field in inner_indexes:
                return IndexNestedLoopPlan(
                    tx, outer_plan, inner_table, inner_layout,
                    inner_indexes[inner_field], outer_field, inner_field
                )

        return None

# =============================================================
# IndexQueryPlanner & create_indexes
# =============================================================

class IndexQueryPlanner:
    def __init__(self, mm, indexes, better_planner=None):
        self.mm = mm
        self.indexes = indexes or {}
        self.better = better_planner

    def createPlan(self, tx, query_data):
        tables = list(query_data['tables'])
        fields = query_data['fields']
        predicate = query_data.get('predicate')

        eq_map = {}
        if predicate:
            for term in predicate.terms:
                res = _extract_eq_constant(term)
                if res:
                    eq_map[res[0]] = res[1]

        plans = {}
        for t in tables:
            layout = self.mm.getLayout(tx, t)
            table_indexes = self.indexes.get(t, {})
            chosen = None
            # Sort so composite (tuple) keys are checked before single-field keys
            for key, idx in sorted(table_indexes.items(), key=lambda x: 0 if isinstance(x[0], tuple) else 1):
                if isinstance(key, tuple) and all(f in eq_map for f in key):
                    chosen = _IndexPlan(tx, t, layout, idx, [eq_map[f] for f in key])
                    break
                if isinstance(key, str) and key in eq_map:
                    chosen = _IndexPlan(tx, t, layout, idx, eq_map[key])
                    break
            plans[t] = chosen or TablePlan(tx, t, self.mm)

        if self.better:
            return self.better.createPlan(
                tx, query_data, plan_overrides=plans, indexes=self.indexes
            )

        curr = plans[tables[0]]
        for t in tables[1:]:
            curr = ProductPlan(curr, plans[t])
        if predicate:
            curr = SelectPlan(curr, predicate)
        return ProjectPlan(curr, *fields)


def create_indexes(db, tx, index_defs=None, composite_index_defs=None):
    index_defs = index_defs or {}
    composite_index_defs = composite_index_defs or {}
    registry = {}

    for t, f_list in index_defs.items():
        registry.setdefault(t, {})
        for f, typ, ln in f_list:
            registry[t][f] = BTreeIndex(tx, f"{t}_{f}", typ, ln)

    for t, c_list in composite_index_defs.items():
        registry.setdefault(t, {})
        for f_names, f_typs, f_lns in c_list:
            registry[t][tuple(f_names)] = CompositeIndex(
                tx, f"{t}_{'_'.join(f_names)}", list(f_names), list(f_typs), list(f_lns)
            )

    for t, idx_map in registry.items():
        layout = db.mm.getLayout(tx, t)
        ts = TableScan(tx, t, layout)
        while ts.nextRecord():
            rid = ts.currentRecordID()
            for key, idx in idx_map.items():
                if isinstance(key, str):
                    val = ts.getVal(key)
                    idx.insert(val.const_value if hasattr(val, 'const_value') else val, rid)
                else:
                    vals = [ts.getVal(f) for f in key]
                    idx.insert(
                        [v.const_value if hasattr(v, 'const_value') else v for v in vals],
                        rid
                    )
        ts.closeRecordPage()

    return registry