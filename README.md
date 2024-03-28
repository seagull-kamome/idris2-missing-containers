master: ![workflow/CI](https://github.com/seagull-kamome/idris2-missing-containers/actions/workflows/ci.yml/badge.svg?branch=master)

# idris2-missing-containers

Idris2で標準ライブラリに欠けているコンテナ類を提供する事を目的としています。

## APIS

### Data.Container

| module    | type       | description                     |
|-----------|------------|---------------------------------|
| IODArray  | IODArray   | Mutable Dependent-typed Array   |
| IOHashMap | IODHashMap | Mutable Dependent-typed HashMap |
| IOHashMap | IOHashMap  | Mutable HashMap                 |
| IOHashSet | IOHashSet  | Mutable HashSet                 |
| IOIntMap  | IODIntMap  | Mutable Dependent-typed IntMap  |
| IOIntMap  | IOIntMap   | Mutable IntMap                  |

### Data.Hash.Algorithm

| module     | type       | description                     |
|------------|------------|---------------------------------|
| FNV        | FNV1a      |                                 |
| MurMur3    | MurMur3    |                                 |
| OneAtATime | OneAtATime |                                 |
| Sip        | SipHash32  |                                 |
| Sip        | SipHash64  |                                 |



