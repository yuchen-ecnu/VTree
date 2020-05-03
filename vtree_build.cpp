#include<iostream>
#include<cstdio>
#include<cstdlib>
#include<cstring>
#include<vector>
#include<ctime>
#include<fstream>
#include<algorithm>
#include <set>
#include<map>
#include<cmath>
#include<queue>
#include<ctime>
#include<metis.h>
#include <sys/time.h>

using namespace std;
const bool DEBUG_ = false;
const char *edge_file;
const int Partition_Part = 4;//fanout of the vtree
const int Naive_Split_Limit = 33;//number of leaf nodes
bool Save_Order_Matrix = false;//Whether need to support route Matrix(If  true can have additional usage)
const int INF = 0x3fffffff;
const bool RevE = false;//Whether need to do some copy, Directed Graph:false，Undirected Graph:true
const bool Distance_Offset = false;//Whether consider the offset of the vehicle.
const bool DEBUG1 = false;
bool NWFIX;

// TODO: TW-Tree Data
//const int DEFAULT_SPEED = 10;// Vehicle default speed (adjust with your dataset).
const int TIME_SLICE_RANGE = 400; //Time slice range
const bool Optimization_KNN_Cut = true;//Optimization for KNN
const bool Memory_Optimization = true; //Optimization for memory (Usually on)
const bool INDEX_Optimization = true;  //Optimization of Index, if need to store more information turn off (usually no need)

struct timeval tv;
long long ts, te;

void TIME_TICK_START() {
    gettimeofday(&tv, nullptr);
    ts = tv.tv_sec * 1000000 + tv.tv_usec;
}

void TIME_TICK_END() {
    gettimeofday(&tv, nullptr);
    te = tv.tv_sec * 1000000 + tv.tv_usec;
}

void TIME_TICK_PRINT(const char *T, int N = 1) { printf("%s RESULT: \t%lld\t (us)\r\n", (T), (te - ts) / N); }

void TIME_TICK_ALL_PRINT(const char *T, int N = 1) { printf("%s RESULT: \t%lld\t (us)\r\n", (T), (te - ts)); }

template<typename T>
ostream &operator<<(ostream &out, const vector<T> &v) {
    out << v.size() << ' ';
    for (int i = 0; i < v.size(); i++)
        out << v[i] << ' ';
    return out;
}

template<typename A, typename B>
ostream &operator<<(ostream &out, const pair<A, B> &p) {
    out << p.first << ' ' << p.second << ' ';
    return out;
}

template<typename T>
istream &operator>>(istream &in, vector<T> &v) {
    int n;
    in >> n;
    v.clear();
    while (n--) {
        T a;
        in >> a;
        v.push_back(a);
    }
    return in;
}

template<typename A, typename B>
istream &operator>>(istream &in, pair<A, B> &p) {
    in >> p.first >> p.second;
    return in;
}

template<typename A, typename B>
ostream &operator<<(ostream &out, const map<A, B> &h) {
    out << h.size() << ' ';
    typename map<A, B>::const_iterator iter;
    for (iter = h.begin(); iter != h.end(); iter++)
        out << iter->first << ' ' << iter->second << ' ';
    return out;
}

template<typename A, typename B>
istream &operator>>(istream &in, map<A, B> &h) {
    int n;
    in >> n;
    h.clear();
    A a;
    B b;
    while (n--) {
        in >> a >> b;
        h[a] = b;
    }
    return in;
}

template<typename T>
void save(ostream &out, T a) {
    out.write((char *) &a, sizeof(a));
}

template<typename T>
void save(ostream &out, vector<T> &a) {
    save(out, (int) a.size());
    for (int i = 0; i < a.size(); i++)save(out, a[i]);
}

template<typename A, typename B>
void save(ostream &out, const pair<A, B> &p) {
    save(out, p.first);
    save(out, p.second);
}

template<typename A, typename B>
void save(ostream &out, const map<A, B> &h) {

    save(out, (int) h.size());
    typename map<A, B>::const_iterator iter;
    for (iter = h.begin(); iter != h.end(); iter++) {
        save(out, iter->first);
        save(out, iter->second);
    }
}

template<typename T>
void read(istream &in, T &a) {
    in.read((char *) &a, sizeof(a));
}

template<typename T>
void read(istream &in, vector<T> &a) {
    int n;
    read(in, n);
    a = vector<T>(n);
    for (int i = 0; i < n; i++)read(in, a[i]);
}

template<typename A, typename B>
void read(istream &in, pair<A, B> &p) {
    read(in, p.first);
    read(in, p.second);
}

template<typename A, typename B>
void read(istream &in, map<A, B> &h) {
    int n;
    read(in, n);
    h.clear();
    A a;
    B b;
    while (n--) {
        read(in, a);
        read(in, b);
        h[a] = b;
    }
}

//Road Network Structure
struct Graph//Struct of the graph
{
    int n, m;//n vertices and m edges, the number starts from 0 to n-1
    int tot;
    vector<int> id;//id[i] is the real number of vertex [i]
    vector<int> head, list, next, cost;//Adjacent Table
    Graph() { clear(); }

    ~Graph() { clear(); }

    friend ostream &operator<<(ostream &out, const Graph &G)//Storage the structure(stdout)
    {
        out << G.n << ' ' << G.m << ' ' << G.tot << ' ' << G.id << ' ' << G.head << ' ' << G.list << ' ' << G.next
            << ' ' << G.cost << ' ';
        return out;
    }

    friend istream &operator>>(istream &in, Graph &G)//Read Instruction(stdout)
    {
        in >> G.n >> G.m >> G.tot >> G.id >> G.head >> G.list >> G.next >> G.cost;
        return in;
    }

    // 行存储结构，head[a]=a的第1个neighbor的ID，next[head[a]]=a的第二个邻居的ID，以此类推实现邻居的按行访问
    void add_D(int a, int b, int c)//add a edge a->b with weight c (directed)
    {
        tot++;
        list[tot] = b;
        cost[tot] = c;
        next[tot] = head[a];
        head[a] = tot;
    }

    void add(int a, int b, int c)// add a edge with weight c in undirected graph a<->b
    {
        add_D(a, b, c);
        add_D(b, a, c);
    }

    void init(int N, int M, int t = 1) {
        clear();
        n = N;
        m = M;
        tot = t;
        head = vector<int>(N);
        id = vector<int>(N);
        list = vector<int>(M * 2 + 2);
        next = vector<int>(M * 2 + 2);
        cost = vector<int>(M * 2 + 2);
    }

    void clear() {
        n = m = tot = 0;
        head.clear();
        list.clear();
        next.clear();
        cost.clear();
        id.clear();
    }

    //Graph Partition
    vector<int> color;//01 color vector
    vector<int> con;// Whether is connected
    //Partition the graph to two parts, and stores to G1, G2,2 METIS algorithm,npart is the number of parts
    // 将图`G`划分为`nparts`,并返回存储了每个点对应的分区color
    vector<int> Split(Graph *G[], int nparts) {
        vector<int> color(n);
        int i;

        if (DEBUG1)printf("Begin-Split\n");
        if (n == nparts) {
            // Partition of lead node(每个vertex各自为1个node)
            for (i = 0; i < n; i++)color[i] = i;
        } else {
            // Partition by metis
            idx_t options[METIS_NOPTIONS];
            memset(options, 0, sizeof(options));
            {
                // initial metis parameter
                METIS_SetDefaultOptions(options);
                options[METIS_OPTION_PTYPE] = METIS_PTYPE_KWAY; // _RB
                options[METIS_OPTION_OBJTYPE] = METIS_OBJTYPE_CUT; // _VOL
                options[METIS_OPTION_CTYPE] = METIS_CTYPE_SHEM; // _RM
                options[METIS_OPTION_IPTYPE] = METIS_IPTYPE_RANDOM; // _GROW _EDGE _NODE
                options[METIS_OPTION_RTYPE] = METIS_RTYPE_FM; // _GREEDY _SEP2SIDED _SEP1SIDED
                /* balance factor, used to be 500 */
                options[METIS_OPTION_UFACTOR] = 500;
                options[METIS_OPTION_CONTIG] = 1;
                options[METIS_OPTION_NUMBERING] = 0;
            }
            idx_t nvtxs = n;
            idx_t ncon = 1;
            //transform
            int *xadj = new idx_t[n + 1];
            int *adj = new idx_t[n + 1];
            int *adjncy = new idx_t[tot - 1];
            int *adjwgt = new idx_t[tot - 1];
            int *part = new idx_t[n];

            int xadj_pos = 1;
            int xadj_accum = 0;
            int adjncy_pos = 0;

            // xadj, adjncy, adjwgt
            xadj[0] = 0;
            int i = 0;
            for (int i = 0; i < n; i++) {

                for (int j = head[i]; j; j = next[j]) {
                    int enid = list[j];
                    xadj_accum++;
                    adjncy[adjncy_pos] = enid;
                    adjwgt[adjncy_pos] = cost[j];
                    adjncy_pos++;
                }
                xadj[xadj_pos++] = xadj_accum;
            }

            // adjust nodes number started by 0

            // adjwgt -> 1
            for (int i = 0; i < adjncy_pos; i++) {
                adjwgt[i] = 1;
            }

            // nparts
            int objval = 0;
            //METIS
            METIS_PartGraphKway(
                    &nvtxs,
                    &ncon,
                    xadj,
                    adjncy,
                    nullptr,
                    nullptr,
                    adjwgt,
                    &nparts,
                    nullptr,
                    nullptr,
                    options,
                    &objval,
                    part
            );
            for (int i = 0; i < n; i++)color[i] = part[i];
            delete[] xadj;
            delete[] adj;
            delete[] adjncy;
            delete[] adjwgt;
            delete[] part;
        }
        //Partation
        int j;
        vector<int> new_id;
        vector<int> tot(nparts, 0), m(nparts, 0);
        for (i = 0; i < n; i++)
            new_id.push_back(tot[color[i]]++);
        for (i = 0; i < n; i++)
            for (j = head[i]; j; j = next[j])
                if (color[list[j]] == color[i])
                    m[color[i]]++;
        for (int t = 0; t < nparts; t++) {
            (*G[t]).init(tot[t], m[t]);
            for (i = 0; i < n; i++)
                if (color[i] == t)
                    for (j = head[i]; j; j = next[j])
                        if (color[list[j]] == color[i])
                            (*G[t]).add_D(new_id[i], new_id[list[j]], cost[j]);
        }
        for (i = 0; i < tot.size(); i++)tot[i] = 0;
        for (i = 0; i < n; i++)
            (*G[color[i]]).id[tot[color[i]]++] = id[i];
        if (DEBUG1)printf("Split_over\n");
        return color;
    }
} G;

struct Matrix//Distance Matrix(1D)
{
    Matrix() : n(0), a(nullptr) {}

    ~Matrix() { clear(); }

    int n;//n*n Matrix
    int *a;

    friend ostream &operator<<(ostream &out, const Matrix &M) {
        out << M.n << ' ';
        for (int i = 0; i < M.n; i++)
            for (int j = 0; j < M.n; j++)
                out << M.a[i * M.n + j] << ' ';
        return out;
    }

    friend istream &operator>>(istream &in, Matrix &M) {
        in >> M.n;
        M.a = new int[M.n * M.n];
        for (int i = 0; i < M.n; i++)
            for (int j = 0; j < M.n; j++)
                in >> M.a[i * M.n + j];
        return in;
    }

    void save_binary(ostream &out) {
        save(out, n);
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                save(out, a[i * n + j]);
    }

    void read_binary(istream &in) {
        read(in, n);
        a = new int[n * n];
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                read(in, a[i * n + j]);
    }

    // filling matrix with value x
    void cover(int x) {
        for (int i = 0; i < n; i++)
            for (int j = 0; j < n; j++)
                a[i * n + j] = x;
    }

    //malloc space and filling matrix with default value {(i,j)=INF,(i,i)=0}
    void init(int N) {
        clear();
        n = N;
        a = new int[n * n];
        for (int i = 0; i < n * n; i++)a[i] = INF;
        for (int i = 0; i < n; i++)a[i * n + i] = 0;// initial (i,i)=0
    }

    //release memory
    void clear() {
        delete[] a;
    }

    //Proof: https://www.cnblogs.com/wd-one/p/4539461.html
    void floyd(Matrix &order)//Calculate the matrix with floyd algorithm, and record result to order(route found)
    {
        int i, j, k;
        for (k = 0; k < n; k++)
            for (i = 0; i < n; i++)
                for (j = 0; j < n; j++)
                    if (a[i * n + j] > a[i * n + k] + a[k * n + j]) {
                        a[i * n + j] = a[i * n + k] + a[k * n + j];
                        order.a[i * n + j] = k;
                    }
    }

    Matrix &operator=(const Matrix &m) {
        if (this != (&m)) {
            init(m.n);
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++)
                    a[i * n + j] = m.a[i * n + j];
        }
        return *this;
    }

    int *operator[](int x) { return a + x * n; }
};

struct Node {//V-Tree Node
    Node() { clear(); }

    // TODO: TW-Tree Data
    vector<vector<map<int, int>>> waypoint_list;//waypoint_list[vertex_idx][time_slice]={vehicle_id,pos}
    vector<vector<int>> vehicle_list;//vehicle_list[local_vertex_idx][vehicle_id]

    int part;//number of son nodes
    int n, father, deep;//n: the number of subgraph, the id of father node,son[2]left son and right son,deep: current depth
    vector<int> son;
    Graph G;//subgraph
    vector<int> color;//which subgraph the node belongs to
    Matrix dist, order;//border distance matrix ,border pass route with floyd k,order=(-1:connected directly)|(-2:connected in parents)|(-3:connected in son nodes)|(-INF:none)
    map<int, pair<int, int>> borders;//<border_vertex_id, <border_index, inner_index>>
    //first:real id of border ;second:<number of border in borders, corresponding nodes(0~n-1)>
    vector<int> border_in_father, border_in_son, border_id, border_id_innode;
    //Border在父节点内部的Index，Border在儿子节点内部的Index，
    //the number of borders in father node and son node, raw id in graph G, number of border in sub node
    vector<int> path_record;//temp record for route
    int cache_vertex_id, cache_bound;// the start id stored in cache, the updated bound in cache(bound had updated end)
    vector<int> cache_dist;
    //cache_dist stores the distance from cache_id to all the borders, only be correct when it small or equal to cache_bound
    vector<int> border_son_id;//Border所在儿子节点的Index
    //the number of son node which border belongs to
    int min_border_dist;//min cached distance of current border in the cache (for KNN cut)
    vector<pair<int, int>> min_car_dist;//the nearest car and the node_id to the border <car_dist,node_id>
    friend ostream &operator<<(ostream &out, const Node &N) {
        out << N.n << ' ' << N.father << ' ' << N.part << ' ' << N.deep << ' ' << N.cache_vertex_id << ' '
            << N.cache_bound << ' ' << N.min_border_dist << ' ';
        for (int i = 0; i < N.part; i++)out << N.son[i] << ' ';
        if (INDEX_Optimization) {
            out << N.color << ' ' << N.dist << ' ' << N.borders << ' ';
            if (Save_Order_Matrix)out << N.order << ' ';
        } else {
            out << N.color << ' ' << N.dist << ' ' << N.borders << ' ' << N.border_in_father << ' ' << N.border_in_son
                << ' ' << N.border_id << ' ' << N.border_id_innode << ' ' << N.path_record << ' ' << N.cache_dist << ' '
                << N.min_car_dist << ' ' << N.border_son_id << ' ';
            if (Save_Order_Matrix)out << N.order << ' ';
        }
        return out;
    }

    friend istream &operator>>(istream &in, Node &N) {
        in >> N.n >> N.father >> N.part >> N.deep >> N.cache_vertex_id >> N.cache_bound >> N.min_border_dist;
        N.son.clear();
        N.son = vector<int>(N.part);
        for (int i = 0; i < N.part; i++)in >> N.son[i];
        if (INDEX_Optimization) {
            in >> N.color >> N.dist >> N.borders;
            if (Save_Order_Matrix)in >> N.order;
        } else {
            in >> N.color >> N.dist >> N.borders >> N.border_in_father >> N.border_in_son >> N.border_id
               >> N.border_id_innode >> N.path_record >> N.cache_dist >> N.min_car_dist >> N.border_son_id;
            if (Save_Order_Matrix)in >> N.order;
        }
        return in;
    }

    void save_binary(ostream &out) {
        save(out, n);
        save(out, father);
        save(out, part);
        save(out, deep);
        save(out, cache_vertex_id);
        save(out, cache_bound);
        save(out, min_border_dist);
        save(out, waypoint_list);
        save(out, vehicle_list);
        for (int i = 0; i < part; i++)save(out, son[i]);
        if (INDEX_Optimization) {
            save(out, color);
            dist.save_binary(out);
            if (Save_Order_Matrix)order.save_binary(out);
            save(out, borders);
        } else {
            save(out, color);
            dist.save_binary(out);
            if (Save_Order_Matrix)order.save_binary(out);
            save(out, borders);
            save(out, border_in_father);
            save(out, border_in_son);
            save(out, border_id);
            save(out, border_id_innode);
            save(out, path_record);
            save(out, cache_dist);
            save(out, min_car_dist);
            save(out, border_son_id);
        }
    }

    void read_binary(istream &in) {
        read(in, n);
        read(in, father);
        read(in, part);
        read(in, deep);
        read(in, cache_vertex_id);
        read(in, cache_bound);
        read(in, min_border_dist);
        read(in, waypoint_list);
        read(in, vehicle_list);
        son.clear();
        son = vector<int>(part);
        for (int i = 0; i < part; i++)read(in, son[i]);
        //printf("read_binary Node n=%d father=%d part=%d deep=%d\n",n,father,part,deep);
        if (INDEX_Optimization) {
            read(in, color);
            dist.read_binary(in);
            if (Save_Order_Matrix)order.read_binary(in);
            read(in, borders);
        } else {
            read(in, color);
            dist.read_binary(in);
            if (Save_Order_Matrix)order.read_binary(in);
            read(in, borders);
            read(in, border_in_father);
            read(in, border_in_son);
            read(in, border_id);
            read(in, border_id_innode);
            read(in, path_record);
            read(in, cache_dist);
            read(in, min_car_dist);
            read(in, border_son_id);
        }
    }

    // initial VTree Node
    void init(int n) {
        part = n;
        son = vector<int>(n);
        for (int i = 0; i < n; i++)son[i] = 0;
    }

    void clear() {
        part = n = father = deep = 0;
        son.clear();
        dist.clear();
        order.clear();
        G.clear();
        color.clear();
        borders.clear();
        border_in_father.clear();
        border_in_son.clear();
        border_id.clear();
        border_id_innode.clear();
        cache_dist.clear();
        cache_vertex_id = -1;
        path_record.clear();
        cache_dist.clear();
        border_son_id.clear();
        min_car_dist.clear();
    }

    //更新直接相连的border之间的距离
    void make_border_edge() {
        int inner_id, i;
        for (auto &border : borders) {
            inner_id = border.second.second;
            for (i = G.head[inner_id]; i; i = G.next[i]) {
                if (color[inner_id] == color[G.list[i]]) continue;
                int id1, id2;
                id1 = border.second.first;
                id2 = borders[G.id[G.list[i]]].first;
                if (dist[id1][id2] > G.cost[i]) {
                    dist[id1][id2] = G.cost[i];
                    order[id1][id2] = -1;
                }
            }
        }
    }
};


struct Vehicle {
    int id;
    vector<int> schedule;
    vector<int> buffer_dist; // buffer_dist[i]: free_time from schedule[i-1] to schedule[i]
    vector<int> deadline; // deadline[i]: latest arrival time of location schedule[i]
    vector<int> distance; // distance[i]: distance from schedule[0] to schedule[i]

    Vehicle(int id, int start, int deadline, int distance) {
        this->id = id;
        this->schedule.push_back(start);
        this->deadline.push_back(deadline);
        this->distance.push_back(distance);
        this->buffer_dist.push_back(0);
    }
};

struct V_Tree {
    int root;
    vector<int> id_in_node;            //which node the vertex belongs to(mapping: node_id -> tree_node)
    vector<vector<int>> car_in_node;//Record the vehicles in the vertex.
    vector<int> car_offset;            //The offset of the vehicle in the vertex.

    vector<Vehicle *> vehicles;

    struct Interface {
        //int cnt1,cnt2;
        V_Tree *tree;//point to the V_Tree(var)
        int tot, size, id_tot;//tot: up bound of vir subscript, size:size of vector,id_tot up bound of memory
        int node_size;//size of vector node
        Node *node;
        vector<int> id;//id of node in vector id
        //sub node information
        vector<int> father;//father node of vir node
        vector<int> border_in_father;//vir node border_in_father
        vector<int> G_id;//real id of the leaf which n=1 in node[0]
        void build_node0(int x)//init node[0] with x
        {
            //cnt2++;
            node[0].borders.clear();
            node[0].borders[G_id[x]] = make_pair(0, 0);
            node[0].border_id[0] = G_id[x];
            node[0].border_in_father[0] = border_in_father[x];
            node[0].father = father[x];
            node[0].deep = node[id[father[x]]].deep + 1;
            {
                int node_id = G_id[x];
                if (!tree->car_in_node[node_id].empty())
                    node[0].min_car_dist[0] = make_pair(0, node_id);
                else
                    node[0].min_car_dist[0] = make_pair(INF, -1);
            }
        }

        Node &operator[](int x) {
            //cnt1++;
            if (id[x] == 0 && Memory_Optimization)
                build_node0(x);
            return node[id[x]];
        }

        friend ostream &operator<<(ostream &out, Interface &I) {
            out << I.tot << ' ' << I.size << ' ' << I.id_tot << ' ' << I.node_size << ' ' << Save_Order_Matrix << ' ';
            for (int i = 0; i < I.node_size; i++)out << I.node[i] << ' ';
            out << I.id << ' ' << I.father << ' ' << I.border_in_father << ' ' << I.G_id << ' ';
            return out;
        }

        friend istream &operator>>(istream &in, Interface &I) {
            in >> I.tot >> I.size >> I.id_tot >> I.node_size >> Save_Order_Matrix;
            delete[]I.node;
            I.node = new Node[I.node_size];
            for (int i = 0; i < I.node_size; i++)in >> I.node[i];
            in >> I.id >> I.father >> I.border_in_father >> I.G_id;
            //Initialize node[0]
            I.node[0].border_id.clear();
            I.node[0].border_id.push_back(0);
            I.node[0].border_in_father.clear();
            I.node[0].border_in_father.push_back(0);
            I.node[0].min_car_dist.clear();
            I.node[0].min_car_dist.push_back(make_pair(0, 0));
            return in;
        }

        void save_binary(ostream &out) {
            save(out, tot);
            save(out, size);
            save(out, id_tot);
            save(out, node_size);
            save(out, Save_Order_Matrix);
            for (int i = 0; i < node_size; i++) {
                node[i].save_binary(out);
            }
            save(out, id);
            save(out, father);
            save(out, border_in_father);
            save(out, G_id);
        }

        void read_binary(istream &in) {
            read(in, tot);
            read(in, size);
            read(in, id_tot);
            read(in, node_size);
            read(in, Save_Order_Matrix);
            delete[]node;
            node = new Node[node_size];
            for (int i = 0; i < node_size; i++) {
                node[i].read_binary(in);
            }
            read(in, id);
            read(in, father);
            read(in, border_in_father);
            read(in, G_id);
            //initialize  node[0]
            node[0].border_id.clear();
            node[0].border_id.push_back(0);
            node[0].border_in_father.clear();
            node[0].border_in_father.push_back(0);
            node[0].min_car_dist.clear();
            node[0].min_car_dist.push_back(make_pair(0, 0));
        }

        ~Interface() { delete[] node; }
    } node;

    friend ostream &operator<<(ostream &out, V_Tree &T) {
        out << T.root << ' ' << T.id_in_node << ' ' << T.car_in_node << ' ' << T.car_offset << ' ';
        out << T.node << ' ';
        return out;
    }

    friend istream &operator>>(istream &in, V_Tree &T) {
        printf("load_begin\n");
        fflush(stdout);
        in >> T.root >> T.id_in_node >> T.car_in_node >> T.car_offset;
        in >> T.node;
        T.node.tree = &T;
        if (INDEX_Optimization) {
            printf("build_border_in_father_son\n");
            fflush(stdout);
            T.build_border_in_father_son();
        }
        return in;
    }

    void save_binary(ostream &out) {
        save(out, root);
        save(out, id_in_node);
        save(out, car_in_node);
        save(out, car_offset);
        node.save_binary(out);
    }

    void read_binary(istream &in) {
        read(in, root);
        read(in, id_in_node);
        read(in, car_in_node);
        read(in, car_offset);
        node.read_binary(in);
        node.tree = this;
        if (INDEX_Optimization) {
            printf("build_border_in_father_son\n");
            fflush(stdout);
            build_border_in_father_son();
        }
    }

    // add border_id(index=inner_index) to node `node_id`
    void add_border(int node_id, int border_id, int inner_index) {
        auto iter = node[node_id].borders.find(border_id); //O(1)
        if (iter == node[node_id].borders.end()) {
            pair<int, int> second = make_pair((int) node[node_id].borders.size(), inner_index);
            node[node_id].borders[border_id] = second;
        }
    }

    // 寻找同一层节点与节点之间的border并标记
    void make_border(int x, const vector<int> &color)//calculate the set of x
    {
        //检查节点X中所有的border并标记
        for (int index = 0; index < node[x].G.n; index++) {
            int id = node[x].G.id[index];
            // 寻找color不同的邻居，如果存在，则顶点id 是Node x的一个border
            for (int j = node[x].G.head[index]; j; j = node[x].G.next[j])
                if (color[index] != color[node[x].G.list[j]]) {
                    add_border(x, id, index);
                    break;
                }
        }
    }

    //Build VTree，current x,number of subgraphs f,current subgraph g
    void build(int x = 1, int f = 1, const Graph &g = G) {
        if (x == 1)//x root
        {
            node.tree = this;
            node.size = G.n * 2 + 2;
            printf("malloc!\n");
            fflush(stdout);
            node.node = new Node[node.size];
            printf("malloc end!\n");
            fflush(stdout);
            node.id = vector<int>(node.size);
            for (int i = 0; i < node.size; i++)node.id[i] = i;
            node.tot = 2;
            root = 1;
            node[x].deep = 1;
            node[1].G = g;
            node.node_size = node.size;
        } else {
            //非root的深度=父节点深度+1
            node[x].deep = node[node[x].father].deep + 1;
        }
        node[x].n = node[x].G.n;
        // 子图中node的数量少于阈值\tau => leaf node => sons=nodes
        if (node[x].G.n < Naive_Split_Limit)node[x].init(node[x].n);
            // inner node => son_cnt = fan_out = Partition_Part
        else node[x].init(Partition_Part);
//        if (node[x].n > 50)printf("x=%d deep=%d n=%d ", x, node[x].deep, node[x].G.n);
        if (node[x].n > f) {
            //initial son id
            int top = node.tot;
            for (int i = 0; i < node[x].part; i++) {
                node[x].son[i] = top + i;
                node[top + i].father = x;
            }
            node.tot += node[x].part;
            //add border between two graph
            Graph **graph;
            graph = new Graph *[node[x].part];
            //孩子节点的Graph地址传入，mut ref直接赋给孩子节点分割后的子图
            for (int i = 0; i < node[x].part; i++)graph[i] = &node[node[x].son[i]].G;
            node[x].color = node[x].G.Split(graph, node[x].part);
            delete[] graph;
            //初始化节点x的border
            make_border(x, node[x].color);
//            if (node[x].n > 50)printf("border=%lu\n", node[x].borders.size());

            // 将当前节点的border传给对应的孩子
            for (auto iter = node[x].borders.begin(); iter != node[x].borders.end(); iter++) {
                //printf("(%d,%d,%d)",iter->first,iter->second.first,iter->second.second);
                node[x].color[iter->second.second] = -node[x].color[iter->second.second] - 1;
            }
            //cout<<endl;
            vector<int> tot(node[x].part, 0);
            for (int i = 0; i < node[x].n; i++) {
                if (node[x].color[i] < 0) {
                    node[x].color[i] = -node[x].color[i] - 1;
                    add_border(node[x].son[node[x].color[i]], node[x].G.id[i], tot[node[x].color[i]]);
                }
                tot[node[x].color[i]]++;
            }
            //递归初始化（划分）子节点
            for (int i = 0; i < node[x].part; i++)
                build(node[x].son[i]);
        } else if (node[x].n > 50)cout << endl;
        //初始化（malloc memory）Distance Matrix
        node[x].dist.init(node[x].borders.size());
        node[x].order.init(node[x].borders.size());
        node[x].order.cover(-INF);
        //计算Distance Matrix (只在根节点执行，一次性初始化整棵树)
        if (x != 1) return;
        //计算border在父节点和儿子节点的Index(辅助)
        printf("begin_build_border_in_father_son\n");
        build_border_in_father_son();
        printf("begin_build_dist\n");
        build_dist1(root);
        printf("begin_build_dist2\n");
        build_dist2(root);
        //calculate the leaf node id of vertex in
        id_in_node.clear();
        for (int i = 0; i < node[root].G.n; i++)id_in_node.push_back(-1);
        for (int i = 1; i < node.tot; i++)
            if (node[i].G.n == 1)
                id_in_node[node[i].G.id[0]] = i;
        {
            //建立car_in_node;
            vector<int> empty_vector;
            empty_vector.clear();
            car_in_node.clear();
            for (int i = 0; i < G.n; i++)car_in_node.push_back(empty_vector);
        }
        if (Memory_Optimization)Memory_Compress();
    }

    // 自底向上构建distance matrix
    void build_dist1(int x = 1) {
        // 递归计算叶子节点
        for (int i = 0; i < node[x].part; i++)
            if (node[x].son[i])
                build_dist1(node[x].son[i]);
        if (node[x].son[0]) {
            //非叶子节点需要构建border与border之间的距离
            node[x].make_border_edge();
            node[x].dist.floyd(node[x].order);
        } else;//leaf
        if (!node[x].father) return;
        int father_id = node[x].father, i, j;
        //计算在父节点中的border_id, 不存在记为-1
        vector<int> id_in_fa(node[x].borders.size());
        for (auto border = node[x].borders.begin(); border != node[x].borders.end(); border++) {
            auto border_in_father = node[father_id].borders.find(border->first);
            if (border_in_father == node[father_id].borders.end()) id_in_fa[border->second.first] = -1;
            else id_in_fa[border->second.first] = border_in_father->second.first;
        }
        // 向父节点传递距离
        for (i = 0; i < (int) node[x].borders.size(); i++)
            for (j = 0; j < (int) node[x].borders.size(); j++) {
                if (id_in_fa[i] == -1 || id_in_fa[j] == -1)continue;
                int *p = &node[father_id].dist[id_in_fa[i]][id_in_fa[j]];
                if ((*p) > node[x].dist[i][j]) {
                    (*p) = node[x].dist[i][j];
                    node[father_id].order[id_in_fa[i]][id_in_fa[j]] = -3;
                }
            }
    }

    //Calculate from top to down as in paper
    void build_dist2(int x = 1) {
        // 计算内部Vertices之间的距离
        if (x != root) node[x].dist.floyd(node[x].order);
        // 当前节点是叶子节点，结束计算
        if (!node[x].son[0])return;
        //calculate the border id in subgraph of current border
        vector<int> id_(node[x].borders.size());
        vector<int> color_(node[x].borders.size());
        for (auto border = node[x].borders.begin(); border != node[x].borders.end(); border++) {
            int c = node[x].color[border->second.second];
            color_[border->second.first] = c;
            int y = node[x].son[c];
            id_[border->second.first] = node[y].borders[border->first].first;
        }
        //Recalculate the subgraph weight
        for (int i = 0; i < (int) node[x].borders.size(); i++)
            for (int j = 0; j < (int) node[x].borders.size(); j++) {
                if (color_[i] != color_[j])continue;
                int y = node[x].son[color_[i]];
                int *p = &node[y].dist[id_[i]][id_[j]];
                if ((*p) > node[x].dist[i][j]) {
                    (*p) = node[x].dist[i][j];
                    node[y].order[id_[i]][id_[j]] = -2;
                }
            }
        // Recursive child nodes
        for (int i = 0; i < node[x].part; i++)
            if (node[x].son[i])build_dist2(node[x].son[i]);
    }

    //calculate the id of border in father/son
    void build_border_in_father_son() {
        int i, j, x, y;
        //Construct cache
        for (x = 1; x < node.tot; x++) {
            //printf("x=%d node.id[x]=%d size=%d\n",x,node.id[x],node.node_size);fflush(stdout);
            //node[x].write();fflush(stdout);
            node[x].cache_dist.clear();
            node[x].min_car_dist.clear();
            node[x].cache_vertex_id = -1;
            for (j = 0; j < node[x].borders.size(); j++) {
                node[x].cache_dist.push_back(0);
                node[x].min_car_dist.push_back(make_pair(INF, -1));
            }
            node[x].border_id.clear();
            node[x].border_id_innode.clear();
            for (i = 0; i < node[x].borders.size(); i++)node[x].border_id.push_back(0);
            for (i = 0; i < node[x].borders.size(); i++)node[x].border_id_innode.push_back(0);
            for (auto iter = node[x].borders.begin(); iter != node[x].borders.end(); iter++) {
                node[x].border_id[iter->second.first] = iter->first;
                node[x].border_id_innode[iter->second.first] = iter->second.second;
            }
            node[x].border_in_father.clear();
            node[x].border_in_son.clear();
            for (i = 0; i < node[x].borders.size(); i++) {
                node[x].border_in_father.push_back(-1);
                node[x].border_in_son.push_back(-1);
            }
            if (node[x].father) {
                y = node[x].father;
                for (auto border = node[x].borders.begin(); border != node[x].borders.end(); border++) {
                    auto border_in_father = node[y].borders.find(border->first);
                    if (border_in_father == node[y].borders.end()) continue;
                    node[x].border_in_father[border->second.first] = border_in_father->second.first;
                }
            }
            if (node[x].son[0]) {
                for (auto iter = node[x].borders.begin(); iter != node[x].borders.end(); iter++) {
                    y = node[x].son[node[x].color[iter->second.second]];
                    auto iter2 = node[y].borders.find(iter->first);
                    if (iter2 != node[y].borders.end())
                        node[x].border_in_son[iter->second.first] = iter2->second.first;
                }
                node[x].border_son_id.clear();
                for (i = 0; i < node[x].borders.size(); i++)
                    node[x].border_son_id.push_back(node[x].son[node[x].color[node[x].border_id_innode[i]]]);
            }
        }
    }

    void Memory_Compress()//Compress the tree in memory make the node with n=1 visual
    {
        printf("Begin Memory Compress! node_size=%d\n", node.node_size);
        int cnt = 0;
        for (int i = 0; i < node.tot; i++)
            if (i == 0 || node.node[i].n > 1)cnt++;
        Node *new_node = new Node[cnt + 1];
        node.node_size = cnt + 1;
        node.id_tot = 1;
        node.border_in_father = node.G_id = node.father = vector<int>(node.tot);
        for (int i = 0; i < node.tot; i++) {
            if (node.node[i].n > 1 || i == 0) {
                node.id[i] = (node.id_tot++);
                new_node[node.id[i]] = node.node[i];
            } else {
                //node.node[i].write();
                new_node[node.id[i] = 0] = node.node[i];
                node.G_id[i] = node.node[i].G.id[0];
                node.father[i] = node.node[i].father;
                node.border_in_father[i] = node.node[i].border_in_father[0];
            }
        }
        delete[]node.node;
        node.node = new_node;
        printf("End Memory Compress! node_size=%d\n", node.node_size);
        fflush(stdout);
    }

    int get_car_offset(int car_id)//get the offset of car_id
    {
        while (car_offset.size() <= car_id)car_offset.push_back(0);
        return car_offset[car_id];
    }

    void push_borders_up(int x, vector<int> &dist1, int type)
    //put the shortest distance from S to x in dist1, then calculate the distance from S to x.father and update dist
    //type = 0 is up, type = 1 is down
    {
        if (node[x].father == 0)return;
        int y = node[x].father;
        vector<int> dist2(node[y].borders.size(), INF);
        for (int i = 0; i < node[x].borders.size(); i++)
            if (node[x].border_in_father[i] != -1)
                dist2[node[x].border_in_father[i]] = dist1[i];
        Matrix &dist = node[y].dist;
        int *begin, *end;
        begin = new int[node[x].borders.size()];
        end = new int[node[y].borders.size()];
        int tot0 = 0, tot1 = 0;
        for (int i = 0; i < dist2.size(); i++) {
            if (dist2[i] < INF)begin[tot0++] = i;
            else if (node[y].border_in_father[i] != -1)end[tot1++] = i;
        }
        if (type == 0) {
            for (int i = 0; i < tot0; i++) {
                int i_ = begin[i];
                for (int j = 0; j < tot1; j++) {
                    int j_ = end[j];
                    if (dist2[j_] > dist2[i_] + dist[i_][j_])
                        dist2[j_] = dist2[i_] + dist[i_][j_];
                }
            }
        } else {
            for (int i = 0; i < tot0; i++) {
                int i_ = begin[i];
                for (int j = 0; j < tot1; j++) {
                    int j_ = end[j];
                    if (dist2[j_] > dist2[i_] + dist[j_][i_])
                        dist2[j_] = dist2[i_] + dist[j_][i_];
                }
            }
        }
        dist1 = dist2;
        delete[] begin;
        delete[] end;
    }

    int find_LCA(int x, int y)//LCA of x and y
    {
        if (node[x].deep < node[y].deep)swap(x, y);
        while (node[x].deep > node[y].deep)x = node[x].father;
        while (x != y) {
            x = node[x].father;
            y = node[y].father;
        }
        return x;
    }

    int search(int S, int T)//Shortest distance from S to T
    {
        if (S == T)return 0;
        //Calculate LCA
        int i, j, k, p;
        int LCA, x = id_in_node[S], y = id_in_node[T];
        if (node[x].deep < node[y].deep)swap(x, y);
        while (node[x].deep > node[y].deep)x = node[x].father;
        while (x != y) {
            x = node[x].father;
            y = node[y].father;
        }
        LCA = x;
        vector<vector<int>> dist(2);
        dist[0].push_back(0);
        dist[1].push_back(0);
        x = id_in_node[S], y = id_in_node[T];
        //naive method as GTree
        for (int t = 0; t < 2; t++) {
            if (t == 0)p = x;
            else p = y;
            while (node[p].father != LCA) {
                push_borders_up(p, dist[t], t);
                p = node[p].father;
            }
            if (t == 0)x = p;
            else y = p;
        }
        vector<int> id[2];//current border id in sequence of LCA border vector
        for (int t = 0; t < 2; t++) {
            if (t == 0)p = x;
            else p = y;
            for (i = j = 0; i < (int) dist[t].size(); i++)
                if (node[p].border_in_father[i] != -1) {
                    id[t].push_back(node[p].border_in_father[i]);
                    dist[t][j] = dist[t][i];
                    j++;
                }
            while (dist[t].size() > id[t].size()) { dist[t].pop_back(); }
        }
        //matched
        int MIN = INF;
        for (i = 0; i < dist[0].size(); i++) {
            int i_ = id[0][i];
            for (j = 0; j < dist[1].size(); j++) {
                k = dist[0][i] + dist[1][j] + node[LCA].dist[i_][id[1][j]];
                if (k < MIN)MIN = k;
            }
        }
        return MIN;
    }

    //TODO: 补充路网点的构建过程
    void build_waypoints(int initial_vehicle_cnt) {
        generate_vehicles(initial_vehicle_cnt);
        // 寻找waypoints并填充到节点上
        map<int, set<int>> waypoints;
        for (auto v:vehicles) {
            for (auto wp: v->schedule) {
                auto it = waypoints.find(wp);
                if (it != waypoints.end()) {
                    it->second.insert(v->id);
                    continue;
                }
                set<int> v_id;
                v_id.insert(v->id);
                waypoints.insert(pair<int, set<int>>(wp, v_id));
            }
        }
        //初始化vehicle list(leaf node)
        queue<int> queue;
        queue.push(1);
        while (!queue.empty()) {
            int x = queue.front();
            if (!node[x].son.empty() && node[node[x].son[0]].n <= 1) {
                //leaf node, 维护vehicle list
                node[x].vehicle_list.resize(node[x].borders.size());
                for (auto &border:node[x].borders) {
                    int border_id = border.second.second;
                    int border_idx = border.first;
                    if (waypoints.find(border_idx) != waypoints.end()) {
                        auto vehicle_set = waypoints.find(border_idx)->second;
                        for (auto v :vehicle_set) {
                            node[x].vehicle_list[border_id].push_back(v);
                        }
                    }
                }
            } else {
                for (int i : node[x].son) {
                    queue.push(i);
                }
            }
            queue.pop();
        }

        // 计算waypoint list
        for (auto v:vehicles) {
            for (int j = 1; j < v->schedule.size(); ++j) {
                int o = v->schedule[j];
                int x = node[id_in_node[o]].father;
                build_waypoint(x, v, j);
            }
        }
    }

    void build_waypoint(int x, Vehicle *v, int pos_idx) {
        int o2 = v->schedule[pos_idx];
        int o2_idx = node[x].borders.find(o2)->second.first;
        //初始化node x的时间分区和waypoint list
        node[x].waypoint_list.resize(node[x].borders.size());
        for (int i = 0; i < node[x].dist.n; ++i) {
            int d2 = node[x].dist[i][o2_idx];
            int d1;
            auto iter = node[x].borders.find(v->schedule[pos_idx - 1]);
            if (iter != node[x].borders.end()) {
                int o1_idx = iter->second.first;
                d1 = node[x].dist[i][o1_idx];
            } else {
                d1 = search(node[x].border_id[i], v->schedule[pos_idx - 1]);
            }
            int detour = d1 + d2 - (v->distance[pos_idx] - v->distance[pos_idx - 1]);
            if (detour > v->buffer_dist[pos_idx - 1])continue;
            if (node[x].waypoint_list[i].size() < detour / TIME_SLICE_RANGE + 1)
                node[x].waypoint_list[i].resize(detour / TIME_SLICE_RANGE + 1);
            node[x].waypoint_list[i][detour / TIME_SLICE_RANGE].insert(make_pair(v->id, pos_idx - 1));
//            if (detour > 0) {
//                printf("detour=%d, vehicle=%d, buffer_dis=%d, x=%d\n", detour, v->id, v->buffer_dist[pos_idx - 1], x);
//            }
        }
        if (node[node[x].father].borders.find(o2) != node[node[x].father].borders.end()) {
            build_waypoint(node[x].father, v, pos_idx);
        }
    }

    void generate_vehicles(int cnt) {
        for (int i = 0; i < cnt; ++i) { // 随机生成5000辆车
            auto v = new Vehicle(i, rand() % G.id.size(), 0, 0);//随机赋值起点
            int current_pos;// 当前位置
            int waypoint_cnt = rand() % 5; //waypoint数量
            for (; waypoint_cnt >= 0; --waypoint_cnt) { //随机生成waypoint
                current_pos = v->schedule.back();
                int step = rand() % 5 + 5; //随机两个waypoint之间的距离(经过的路口数量)
                for (; step >= 0; --step) {
                    vector<int> neighbors;
                    for (int j = G.head[current_pos]; j; j = G.next[j]) {
                        neighbors.push_back(G.list[j]);
                    }
                    // 随机选择一个邻居游走
                    int direction = rand() % neighbors.size();
                    current_pos = neighbors[direction];
                }
                double buf_factor = rand() % 5 / 10.0 + 1.1;
                int from = v->schedule.back();
                int distance = this->search(from, current_pos);
                int prev_dist = v->distance.back();
                v->deadline.push_back(buf_factor * distance + prev_dist);
                v->distance.push_back(distance + prev_dist);
                v->schedule.push_back(current_pos);
                v->buffer_dist.push_back(0); // 占位
            }

            // Calculate buffer_dist O(n)
            v->buffer_dist.back() = 10 * 60 * 17; //60 km/h * 10 min //TODO: should be infinity?
            if (v->schedule.size() > 1)
                v->buffer_dist[v->buffer_dist.size() - 2] = v->deadline.back() - v->distance.back();
            for (int cur_pos = v->schedule.size() - 3; cur_pos >= 0; --cur_pos) {
                v->buffer_dist[cur_pos] = min(v->buffer_dist[cur_pos + 1],
                                              v->deadline[cur_pos + 1] - v->distance[cur_pos + 1]);
            }
            vehicles.push_back(v);
        }
    }

    // 给定request查询候选车辆(source,target,number,max waiting,deadline)
    void find_candidate_vehicle(int s, int t, int n, int w, int d) {
        int x = node[id_in_node[s]].father;
        set<int> candidate_vehicles;
        while (x != 1) {//x==1 is root
            set<int> candidate_border;
            for (int i = 0; i < node[x].dist.n; ++i) {
                int border_idx = node[x].borders.find(i)->second.second; // 叶子节点都是border
                int dist = node[x].dist[i][border_idx];
                //遍历可能的TIME_RANGE里面的vehicle
                for (int j = 0; j < node[x].waypoint_list[i].size(); ++j) {
                    if ((j + 1) * TIME_SLICE_RANGE + dist >= w)break;
                    for (auto v : node[x].waypoint_list[i][j])
                        candidate_vehicles.insert(v.first);
                }
                int border_id = node[x].borders.find(i)->second.first;
                if (node[x].border_in_father[border_id] != -1)
                    candidate_border.insert(node[x].border_in_father[border_id]);
            }
            x = node[x].father;
        }
    }
} tree;


void init() {
    srand(747929791);
}

void read() {
    printf("begin read\n");
    FILE *in = nullptr;
    in = fopen(edge_file, "r");
    cout << "Open file success." << endl;
    fscanf(in, "%d %d\n", &G.n, &G.m);
    cout << G.n << " " << G.m << endl;
    cout << "Read graph size correct." << endl;
    G.init(G.n, G.m);
    for (int i = 0; i < G.n; i++)G.id[i] = i;
    cout << "Initial graph success." << endl;
    int i, j, k, l;
    for (i = 0; i < G.m; i++)//Load edge
    {
        fscanf(in, "%d %d %d\n", &j, &k, &l);
        if (NWFIX) {
            if (RevE == false) G.add_D(j, k, l); //Undirected
            else G.add(j, k, l);//Directed
        } else {
            if (RevE == false) G.add_D(j - 1, k - 1, l); //Undirected
            else G.add(j - 1, k - 1, l); //Directed
        }
    }
    cout << "Load edge finished." << endl;
    fclose(in);
}

void save_binary(const string &file_name) {
    printf("begin save_binary\n");
    ofstream out(file_name.c_str());
    save(out, G.n);
    tree.save_binary(out);
    out.close();
    printf("save_binary_over\n");
}

int main(int argc, char *argv[]) {
    if (argc < 3) {
        printf("Build VTree and save use './vtree_gen_index  input_edge_file output_file'\n");
        return 0;
    }
    edge_file = argv[1];
    init();
    read();
    tree.build();
    tree.build_waypoints(10000);
    save_binary(argv[2]); //save index tree
    for (int i = 0; i < tree.vehicles.size(); ++i) {
        delete tree.vehicles[i];
    }
    printf("Build and Save Finished\n");

    printf("Program Finished.\n");
    fflush(stdout);

    return 0;
}
