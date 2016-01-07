//------------------------------------------------------------------------------
/// @file
/// @brief    HPCAnswer.hpp の実装 (解答記述用ファイル)
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2015 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください

//------------------------------------------------------------------------------

#include "HPCAnswer.hpp"
#include "HPCMath.hpp"
#include <vector>
#include <queue>
#include <cstring>
#include <iostream>
#include <algorithm>


using namespace std;
typedef long long ll;

/// プロコン問題環境を表します。
namespace hpc {
    const int dx[4] = {1, 0, -1, 0};
    const int dy[4] = {0, 1, 0, -1};
    const Action action[4] = {Action_MoveRight, Action_MoveUp, Action_MoveLeft, Action_MoveDown};
    const int INF = 1e9;
    // 調べるべき点(最後に empty にする)
    vector<Pos> points;
    // 幅優先探索での距離を管理する(Init で初期化する)
    int memo[50][50];
    // 最短経路で進んだ際の直前の動き(Init で初期化しないけど大丈夫)
    int prev[50][50];
    // ある場所からある場所へ行く最短経路 Action (最後に すべて empty にする)
    vector<Action> minPath[20][20];
    // ある場所からある場所へ行く最短距離
    int dist[20][20];
    // 配達先の集合が与えられた時の, 配達する順番
    vector<int> bestPerm[1<<18];
    // 配達先の集合が与えられた時の, 配達コスト
    int bestCost[1<<18];
    // bitDP のメモ
    int bitDP[1<<18][18];
    // 最善のわけかた
    ll bestSelect;
    // 最善のわけかた01/23
    // 集合を引数にして, 1 を選ぶ集合を返す
    int bestSelect02[2][1<<18];
    // 最善のわけかた01/23 におけるコスト
    int bestCost02[2][1<<18];
    // 各時間に積み込むべき荷物
    vector<vector<int> > bestDiv;
    // 各時間の移動
    vector<vector<Action> > bestAction;
    // 各状態における重さの合計
    int stateWeight[1<<18];
    // 配達先で時間が指定されている集合
    int confirmSet[4];
    // 時間が指定されていない配達先の配列
    vector<int> uncertainSet;
    // 集合を表す bit 列を uncertainSet 用に置き換えた集合に変換する
    int setToUncertainSet[1<<18];

    // bitDP
    // n: 配達先の数 state: 状態
    int dfs(int state, int now, int n, const Stage& aStage) {
        int& ret = bitDP[state][now];
        if (ret >= 0) return ret;
        if (state==(1<<(n+1))-1) {
            return ret = dist[now][n]*3;
        }
        int weight = stateWeight[state^(1<<n)];
        ret = INF;
        for (int i = 0; i < n; i++) {
            if ((state>>i)&1) continue;
            ret = min(ret, weight*dist[i][now] + dfs(state|(1<<i), i, n, aStage));
        }
        return ret;
    }
    // 01, 23 グループで最適な集合のわけかた
    // n: 配達先の数 offset: 01 か 23 か
    void calc(int n, int offset, const Stage& aStage) {
        for (int s = 0; s < 1<<n; s++) bestCost02[offset][s] = INF;
        int cnt = uncertainSet.size();
        for (int s0 = 0; s0 < 1<<cnt; s0++) {
            int ss0 = setToUncertainSet[s0]|confirmSet[2*offset];
            if (stateWeight[ss0^((1<<n)-1)] > 18) continue;
            int sup = 0;
            for (int i = 0; i < cnt; i++) if (((s0>>i)&1)==0) sup |= 1<<uncertainSet[i];
            int sub = sup;
            do {
                int ts1 = confirmSet[1+2*offset] | sub;
                if (stateWeight[ts1^((1<<n)-1)] <= 18) {
                    int ss = ss0|ts1;
                    if (bestCost02[offset][ss] > bestCost[ss0]+bestCost[ts1]) {
                        bestCost02[offset][ss] = bestCost[ss0]+bestCost[ts1];
                        bestSelect02[offset][ss] = ts1;
                    }
                }
                sub = (sub-1) & sup;
            } while (sub != sup);
        }
    }

    //------------------------------------------------------------------------------
    /// 各ステージ開始時に呼び出されます。
    ///
    /// ここで、各ステージに対して初期処理を行うことができます。
    ///
    /// @param[in] aStage 現在のステージ。
    void Answer::Init(const Stage& aStage) {
        // まずグラフを作る
        int H = aStage.field().height();
        int W = aStage.field().width();
        for (int i = 0; i < 4; i++) confirmSet[i] = 0;
        // 調べるべき点を列挙する
        // 同時に配達先が確定してるかしてないかを調べる
        // 配達先
        int transportCount = aStage.items().count();
        for (int i = 0; i < transportCount; i++) {
            points.push_back(aStage.items()[i].destination());
            int period = aStage.items()[i].period();
            if (period == -1) uncertainSet.push_back(i);
            else confirmSet[period] |= 1<<i;
        }
        // setToUncertainSet を作る
        {
            int n = uncertainSet.size();
            for (int s = 0; s < 1<<n; s++) {
                int ss = 0;
                for (int i = 0; i < n; i++) {
                    if ((s>>i)&1) ss |= 1<<uncertainSet[i];
                }
                setToUncertainSet[s] = ss;
            }
        }
        // スタート地点
        points.push_back(aStage.field().officePos());
        // 各頂点への最短経路を minpath にメモする
        for (int i = 0; i < (int)(points.size()); i++) {
            // 幅優先探索
            Pos p = points[i];
            for (int j = 0; j < H; j++) for (int k = 0; k < W; k++) memo[j][k] = INF;
            memo[p.y][p.x] = 0;
            queue<Pos> que;
            que.push(p);
            while (!que.empty()) {
                Pos pos = que.front(); que.pop();
                for (int k = 0; k < 4; k++) {
                    int ny = pos.y+dy[k];
                    int nx = pos.x+dx[k];
                    if (ny < 0 || ny >= H || nx < 0 || nx >= W) continue;
                    if (aStage.field().isWall(nx, ny)) continue;
                    if (memo[ny][nx] > memo[pos.y][pos.x]+1) {
                        memo[ny][nx] = memo[pos.y][pos.x] + 1;
                        prev[ny][nx] = k;
                        que.push(Pos(nx, ny));
                    }
                }
            }
            // 各頂点への最短経路を minpath にメモする
            for (int j = 0; j < (int)(points.size()); j++) {
                Pos now = points[j];
                dist[i][j] = memo[now.y][now.x];
                while (now != p) {
                    int k = prev[now.y][now.x];
                    minPath[i][j].push_back(action[k]);
                    now.y -= dy[k];
                    now.x -= dx[k];
                }
                reverse(minPath[i][j].begin(), minPath[i][j].end());
            }
        }
        // stateWeight の計算
        for (int s = 0; s < (1<<transportCount); s++) {
            int weight = 3;
            for (int i = 0; i < transportCount; i++) {
                if (((s>>i)&1) == 0) weight += aStage.items()[i].weight();
            }
            stateWeight[s] = weight;
        }
        // bitDP する
        memset(bitDP, -1, sizeof(bitDP));
        for (int s = 0; s < 1<<transportCount; s++) {
            if ((stateWeight[s] > 18)) continue;
            bool ng = false;
            int ns = ((1<<(transportCount+1))-1) ^ s;
            for (int i = 0; i < 4; i++) for (int j = i+1; j < 4; j++) {
                if ((ns&confirmSet[i]) != 0 && (ns&confirmSet[j]) != 0) ng = true;
            }
            if (ng) continue;
            dfs(s|(1<<transportCount), transportCount, transportCount, aStage);
        }
        // それぞれの状態について, 最適な順列を求める
        for (int s = 0; s < (1<<transportCount); s++) {
            vector<int> perm;
            if (s==0) {
                bestCost[s] = 0;
                bestPerm[s] = perm;
                continue;
            }
            // state: すでに通った配達先
            int state = s^((1<<(transportCount+1))-1), now = transportCount;
            if (stateWeight[state^(1<<transportCount)] > 18) continue;
            bool ng = false;
            int ns = ((1<<(transportCount+1))-1) ^ state;
            for (int i = 0; i < 4; i++) for (int j = i+1; j < 4; j++) {
                if ((ns&confirmSet[i]) != 0 && (ns&confirmSet[j]) != 0) ng = true;
            }
            if (ng) continue;
            bestCost[s] = bitDP[state][now];
            perm.push_back(now);
            while (state != (1<<(transportCount+1))-1) {
                int weight = stateWeight[state^(1<<transportCount)];
                for (int i = 0; i < transportCount; i++) {
                    if ((state>>i)&1) continue;
                    if (bitDP[state][now] == bitDP[state|(1<<i)][i] + weight*dist[now][i]) {
                        perm.push_back(i);
                        state |= 1<<i;
                        now = i;
                        break;
                    }
                }
            }
            perm.push_back(transportCount);
            bestPerm[s] = perm;
        }
        // 01, 23 で最適な荷物の分け方を考える
        calc(transportCount, 0, aStage);
        calc(transportCount, 1, aStage);
        // 最善の荷物の分け方を選ぶ
        bestSelect = 0;
        int best = INF, bests = 0;
        {
            int n = uncertainSet.size();
            for (int s = 0; s < 1<<n; s++) {
                int s0 = 0, s2 = 0;
                for (int i = 0; i < n; i++) {
                    if ((s>>i)&1) s0 |= 1<<uncertainSet[i];
                    else s2 |= 1<<uncertainSet[i];
                }
                s0 |= confirmSet[0]|confirmSet[1];
                s2 |= confirmSet[2]|confirmSet[3];
                if (best > bestCost02[0][s0] + bestCost02[1][s2]) {
                    best = bestCost02[0][s0] + bestCost02[1][s2];
                    bests = s;
                }
            }
            bestSelect = 0;
            int s0 = 0, s2 = 0;
            for (int i = 0; i < n; i++) {
                if ((bests>>i)&1) s0 |= 1<<uncertainSet[i];
                else s2 |= 1<<uncertainSet[i];
            }
            s0 |= confirmSet[0]|confirmSet[1];
            s2 |= confirmSet[2]|confirmSet[3];
            int ss0 = bestSelect02[0][s0]^s0;
            int ss1 = bestSelect02[0][s0];
            int ss2 = bestSelect02[1][s2]^s2;
            int ss3 = bestSelect02[1][s2];
            for (int i = transportCount-1; i >= 0; i--) {
                if ((ss0>>i)&1) bestSelect = bestSelect*4+0;
                if ((ss1>>i)&1) bestSelect = bestSelect*4+1;
                if ((ss2>>i)&1) bestSelect = bestSelect*4+2;
                if ((ss3>>i)&1) bestSelect = bestSelect*4+3;
            }
        }
        // bestselect の情報から 答えを求める
        bestDiv.resize(4); bestAction.resize(4);
        for (int i = 0; i < 4; i++) {
            bestDiv.clear();
            bestAction.clear();
        }
        for (int i = 0; i < transportCount; i++) {
            bestDiv[bestSelect&3].push_back(i);
            bestSelect /= 4;
        }
        for (int i = 0; i < 4; i++) {
            int s = 0;
            for (int el : bestDiv[i]) s |= 1<<el;
            for (int j = 0; j < (int)(bestPerm[s].size())-1; j++) {
                for (Action ac : minPath[bestPerm[s][j]][bestPerm[s][j+1]]) bestAction[i].push_back(ac);
            }
            bestAction[i].push_back(Action_TERM);
        }
    }

    //------------------------------------------------------------------------------
    /// 各配達時間帯開始時に呼び出されます。
    ///
    /// ここで、この時間帯に配達する荷物をトラックに積み込みます。
    /// どの荷物をトラックに積み込むかを決めて、引数の aItemGroup に対して
    /// setItem で荷物番号を指定して積み込んでください。
    ///
    /// @param[in] aStage 現在のステージ。
    /// @param[in] aItemGroup 荷物グループ。
    void Answer::InitPeriod(const Stage& aStage, ItemGroup& aItemGroup)
    {
        for (int el : bestDiv[aStage.period()]) aItemGroup.addItem(el);
    }

    //------------------------------------------------------------------------------
    /// 各ターンでの動作を返します。
    ///
    /// @param[in] aStage 現在ステージの情報。
    ///
    /// @return これから行う動作を表す Action クラス。
    Action Answer::GetNextAction(const Stage& aStage)
    {
        static int now = 0, period = 0;
        if (period != aStage.period()) {
            period = aStage.period();
            now = 0;
        }
        Action a = bestAction[aStage.period()][now];
        //cout << period << "  " << now << "  " << (int)(a) << endl;
        now++;
        if (now == (int)(bestAction[aStage.period()].size())-1) now = 0;
        return a;
    }

    //------------------------------------------------------------------------------
    /// 各配達時間帯終了時に呼び出されます。
    ///
    /// ここで、この時間帯の終了処理を行うことができます。
    ///
    /// @param[in] aStage 現在のステージ。
    /// @param[in] aStageState 結果。Playingならこの時間帯の配達完了で、それ以外なら、何らかのエラーが発生した。
    /// @param[in] aCost この時間帯に消費した燃料。エラーなら0。
    void Answer::FinalizePeriod(const Stage& aStage, StageState aStageState, int aCost)
    {
        if (aStageState == StageState_Failed) {
            // 失敗したかどうかは、ここで検知できます。
            //cout << "period fail" << endl;
        } else {
            //cout << "period clear!" << endl;
        }
    }

    //------------------------------------------------------------------------------
    /// 各ステージ終了時に呼び出されます。
    ///
    /// ここで、各ステージに対して終了処理を行うことができます。
    ///
    /// @param[in] aStage 現在のステージ。
    /// @param[in] aStageState 結果。Completeなら配達完了で、それ以外なら、何らかのエラーが発生した。
    /// @param[in] aScore このステージで獲得したスコア。エラーなら0。
    void Answer::Finalize(const Stage& aStage, StageState aStageState, int aScore)
    {
        // minPath を clear する
        for (int i = 0; i < 20; i++) for (int j = 0; j < 20; j++) minPath[i][j].clear();
        // points を clear する
        points.clear();
        // uncertainSet を clear する
        uncertainSet.clear();
        if (aStageState == StageState_Failed) {
            // 失敗したかどうかは、ここで検知できます。
            //cout << "stage fail" << endl;
        }
        else if (aStageState == StageState_TurnLimit) {
            // ターン数オーバーしたかどうかは、ここで検知できます。
        } else {
            //cout << "stage clear!" << endl;
        }
    }
}

//------------------------------------------------------------------------------
// EOF
