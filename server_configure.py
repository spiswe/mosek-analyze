#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
    Author : spisw
    Date   : 2018/5/24
    File   : server_configure
"""
import os
from src.lib.static import ErrorCode
from engines.base import BaseEngine


class ServerConfSug(BaseEngine):
    """
    """

    def __init__(self, *args, **kwargs):
        self.args = args
        self.kwargs = kwargs
        super(ServerConfSug, self).__init__()

    def _moudle_register(self):
        return [ErrorCode, BaseEngine]

    def run(self, *args, **kwargs):
        import mosek
        import random

        # define
        CPU = 0
        MEM = 1
        DISK = 2
        TS = 3  # amount of PRI + STD
        PRI = 4
        STD = 5
        WEIGHT = 6
        inf = 0.0

        # TEMPLATE_DEFINE = [CPU, MEM, DISK, TS, PRI, STD, WEIGHT]
        templates_id, templates, server_id, servers = [], [], [], []
        re = []

        for server_info in kwargs["servers"]:
            if server_info[1][0] > 0 and server_info[1][1] > 0 and server_info[1][2] > 0:
                server_id.append(server_info[0])
                servers.append(server_info[1])

        for template_info in kwargs["templates"]:
            if template_info[1][0] > 0 and template_info[1][1] > 0 and template_info[1][2] > 0:
                templates_id.append(template_info[0])
                templates.append(template_info[1])

        if not templates_id or not server_id:
            for i in range(len(templates_id)):
                re.append(dict(id=templates_id[i], plan=[]))
            return ErrorCode.success, re
        # templates_id, templates = [x[0] for x in kwargs["templates"]], [x[1] for x in kwargs["templates"]]
        # server_id, servers = [x[0] for x in kwargs["servers"]], [x[1] for x in kwargs["servers"]]

        numserver = len(servers)
        numtemplate = len(templates)

        # c = [x[WEIGHT] for x in templates] * numserver
        c = [x[WEIGHT] * (x[CPU] + x[MEM] + x[DISK]) for x in templates] * numserver

        # 注意浅拷贝
        clause = [numtemplate * numserver * [0] for _ in range(3 * numserver + numserver * numtemplate)]

        # set constraints functions
        for i in range(numserver):
            j = i
            clause[j][i * numtemplate: (i * numtemplate + numtemplate)] = [t[CPU] for t in templates]

            j += numserver
            clause[j][i * numtemplate: (i * numtemplate + numtemplate)] = [t[MEM] for t in templates]

            j += numserver
            clause[j][i * numtemplate: (i * numtemplate + numtemplate)] = [t[DISK] for t in templates]

            j += numserver
            for k in range(numtemplate):
                for s in range(numserver):
                    clause[j][s * numtemplate + k] = (1 - templates[k][TS]) if s == i else 1
                j += numserver

        # Bound keys for constraints 3 * count(server) + count(template) * count(server) = (3 + 4) * 5
        bkc = 3 * numserver * [mosek.boundkey.ra] + numserver * numtemplate * [mosek.boundkey.lo]
        blc = (3 * numserver + numtemplate * numserver) * [0]
        buc = [x[CPU] for x in servers] + [x[MEM] for x in servers] + [x[DISK] for x in servers] \
              + numserver * numtemplate * [+inf]

        bkx = numserver * numtemplate * [mosek.boundkey.lo]
        blx = numserver * numtemplate * [0]
        bux = numserver * numtemplate * [+inf]

        # 条件做矩阵转置
        clause_T = [[r[col] for r in clause] for col in range(len(clause[0]))]
        asub = [[i for i in range(len(col)) if col[i]] for col in clause_T]
        aval = [[i for i in col if i] for col in clause_T]

        numvar = len(bkx)
        numcon = len(bkc)

        with mosek.Env() as env:
            with env.Task(0, 0) as task:
                task.appendcons(numcon)
                task.appendvars(numvar)

                for j in range(numvar):
                    task.putcj(j, c[j])
                    task.putvarbound(j, bkx[j], blx[j], bux[j])
                    task.putacol(j, asub[j], aval[j])

                task.putconboundlist(range(numcon), bkc, blc, buc)
                task.putobjsense(mosek.objsense.maximize)
                task.putvartypelist([x for x in range(len(c))], len(c) * [mosek.variabletype.type_int])
                task.putdouparam(mosek.dparam.mio_max_time, 60.0)
                task.optimize()
                task.solutionsummary(mosek.streamtype.msg)
                prosta = task.getprosta(mosek.soltype.itg)
                solsta = task.getsolsta(mosek.soltype.itg)
                xx = [0.] * numvar
                task.getxx(mosek.soltype.itg, xx)
                # print(xx)
                xx = [int(x) for x in xx]
                result = [xx[i: i + numtemplate] for i in range(0, len(xx), numtemplate)]
                result = [(server_id[r], result[r]) for r in range(len(result))]

                for i in range(len(templates_id)):
                    flag = []
                    re_by_template = [x[1][i] for x in result]
                    # if plan exists
                    init_re = [[] for _ in range((sum(re_by_template) // templates[i][TS]))]
                    if init_re:
                        for r in range(len(init_re)):
                            for _ in re_by_template:
                                if max(re_by_template) == 0:
                                    init_re[r].append(-1)
                                else:
                                    idx = re_by_template.index(max(re_by_template))
                                    if idx in flag:
                                        for xx in range(len(re_by_template)):
                                            if xx in flag:
                                                continue
                                            else:
                                                if re_by_template[xx] == 0:
                                                    continue
                                                else:
                                                    idx = xx
                                                    break
                                    init_re[r].append(server_id[idx])
                                    re_by_template[idx] -= 1
                                    flag.append(idx)
                                if len(init_re[r]) == templates[i][TS]:
                                    flag = []
                                    random.shuffle(init_re[r])
                                    random.shuffle(init_re[r])
                                    break
                    re.append(dict(id=templates_id[i], plan=init_re))

                return ErrorCode.success, re

                # if solsta in [mosek.solsta.integer_optimal, mosek.solsta.near_integer_optimal]:
                #     return ErrorCode.success, re
                # else:
                #     return ErrorCode.fail, []


def main():
    # print(ServerConfSug.moudle_register())
    s = ServerConfSug()

    info = dict(templates=[("t0", [1, 1, 20, 3, 1, 2, 1]),
                           ("t1", [2, 4, 20, 4, 2, 2, 3]),
                           ("t2", [4, 8, 30, 1, 1, 0, 1]),
                           ("t3", [4, 16, 40, 1, 1, 0, 1])],)

    info = dict(templates=[("t0", [1, 1, 20, 3, 1, 2, 1]),
                           ("t1", [2, 4, 20, 4, 2, 2, 3]),
                           ("t2", [4, 8, 30, 1, 1, 0, 1]),
                           ("t3", [4, 16, 40, 1, 1, 0, 1])],
                servers=[("s0", [16, 60, 400]),
                         ("s1", [32, 48, 500]),
                         ("s2", [16, 100, 1024]),
                         ("s3", [48, 64, 512]),
                         ("s4", [16, 32, 400])])

    print(s.run(**info))
    return


if __name__ == "__main__":
    main()
