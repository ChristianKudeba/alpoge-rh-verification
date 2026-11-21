# Separately checked resonant norm-transfer helpers

These four modules passed native checks against the pinned archive. They are
not part of the aggregate entry point. Their manifest and checker logs are
beside the sources.

They turn a nonzero algebraic norm witness into an integer valuation bound,
transfer that bound to the actual rank-four Selmer data, and collect finitely
many root-trace witnesses. The required norm witness and the original
admissibility/inequality inputs remain explicit. They do not supply the missing
uniform resonant bound or settle the low-twist pair p=3,e=1.

The larger rank-four witness-factory drafts are excluded because their full
import check could not complete on this host: loading the roughly 25,000-module
dependency set exceeded its memory-mapping count limit. The checked helpers
here do not rely on accepting those drafts.
