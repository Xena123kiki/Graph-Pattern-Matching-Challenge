/**
* @file backtrack.cc
*
*/

/* [AL_HW2] Subgraph matching chellenge
* Team :: Eunchae Gong, Woojin Cha
* Contents :: Implementation of DAF algorithm to find subgraph matching probelm
* Date :: 2021-06-08
*/

/* Caution :: You have to delete file result.txt for every execution! */

#include "backtrack.h"
#include <numeric>

Backtrack::Backtrack() {}
Backtrack::~Backtrack() {}

#include <queue>
using namespace std;

const int MAX = 1000;
bool check_bfs[MAX];

string filePath = "result.txt";
ofstream writeFile(filePath.data());

/* BFS :: Do Breath First Search, staring from the root then save BFS order to order vector. */
void BFS(std::vector<int> &order, int root, const Graph &query){
queue<int> q;
q.push(root);
check_bfs[root] = true;

// Do BFS search untill queue is empty
while(!q.empty()){
int current = q.front();
// Add current vertex to order vector while deleting it from the queue.
q.pop();
order.push_back(current);

// For all vertexes negihboring to current vertex, push neighbor vertex to queue if it is not visited yet.
for (int offset = query.GetNeighborStartOffset(current); offset < query.GetNeighborEndOffset(current); offset++) { //Q - getNeigborstartoffset?
int next = query.GetNeighbor(offset);

if(!check_bfs[next]){
check_bfs[next] = true;
q.push(next);
}
}
}
}

/* buildDAG :: Make query graph DAG to real directed acyclic graph by deleting all existing DAG[parent][child]. */
void buildDAG(std::vector<std::vector<int>> &DAG, std::vector<int> order, int idx) {
// Set i-th order vertex as parent.
int parent = order[idx];

// Do following operation for all vertexes connected to parent vertex.
for (int i = 0; i < DAG[parent].size(); i++) {
// Set i-th order vertex as child.
int child = DAG[parent][i];

// If there is DAG[child][parent] in DAG[child] vector, then delete it.
if (count(DAG[child].begin(), DAG[child].end(), parent)) {
DAG[child].erase(remove(DAG[child].begin(), DAG[child].end(), parent), DAG[child].end());
}
}

// Do upper operation for all vertexes in query graph.
if (idx < order.size() - 1) {
buildDAG(DAG, order, idx+1);
}
}


/* get_match_order :: Find out all possible matching cases of {parent, child} from DAG, then save those information as path. */
void get_match_order(const Graph &data, const Graph &query, const CandidateSet &cs, std::vector<std::vector<int>> &DAG, std::vector<std::vector<int>> &path, int current) {

// Do following operations for all child vertexes of query DAG.
std::vector<int> num_candidates;
for (int i = 0; i < DAG[current].size(); i++) {
int child = DAG[current][i];
num_candidates.push_back(DAG[child].size());
}
std::vector<std::size_t> index (DAG[current].size());
std::iota(index.begin(), index.end(), 0);
std::sort(index.begin(), index.end(), [&](size_t a, size_t b) { return num_candidates[a] < num_candidates[b]; });

for (int i = 0; i < DAG[current].size(); i++) {
// Set i-th current vertex's child as child.
int child = DAG[current][index[i]];

// Make pair of {parent, child}.
std::vector<int> tmp = {current, child};

// If {parent, child} pair is not duplicating then add this pair end of the path.
if (!count(path.begin(), path.end(), tmp)) {
path.push_back(tmp);

// Recursive call for checking all child nodes.
get_match_order(data, query, cs, DAG, path, child);
}
}
}

// M means partial embedding path.
// idx means verified number of {parent, child} pair from match_order. If idx equals match_order.size then we find complete embeddings.
/* backtrack :: */
void backtrack(const Graph &data, const Graph query, const CandidateSet &cs, std::vector<std::vector<int>> match_order, std::vector<int> &M, int idx) {
// If idx equals match_order.size then we find complete embeddings.
if (idx == match_order.size()) {

if (writeFile.is_open()) {
writeFile << "a ";
for (int i = 0; i < M.size(); i++) {
writeFile << M[i] << " ";
}
writeFile << "\n";
}

return;
}

// Start of backtracking.
else if (M.size() == 0) {

int root = match_order[idx][0];

for (int i = 0; i < cs.GetCandidateSize(root); i++) {
int root_candidate = cs.GetCandidate(root, i);
std::vector<int> new_M;
new_M.resize(query.GetNumVertices());
for (int j = 0; j < new_M.size(); j++) {
new_M[j] = -1;
}
new_M[root] = root_candidate;
backtrack(data, query, cs, match_order, new_M, idx);
}
}

// Still working to find out complete embedding. (Still partial embedding)
else {

int parent = match_order[idx][0];
int child = match_order[idx][1];

int parent_candidate = M[parent];
if (M[child] != -1) { // TODO: what if M[child] is exist, but M[child] == 0?
if (data.IsNeighbor(parent_candidate, M[child])) {
backtrack(data, query, cs, match_order, M, idx + 1);
}
else {
return;
}
}
else {
for (int j = 0; j < cs.GetCandidateSize(child); j++) {
int child_candidate = cs.GetCandidate(child, j);

if (data.IsNeighbor(parent_candidate, child_candidate)) {
std::vector<int> new_M;
for (int m = 0; m < M.size(); m++) {
new_M.push_back(M[m]);
}
new_M[child] = child_candidate;

backtrack(data, query, cs, match_order, new_M, idx + 1);
// return;
}
}
}
}
}

/* PrintAllMatches :: Find out all embeddings of query graph in Data graph under the specific matching order. */
void Backtrack::PrintAllMatches(const Graph &data, const Graph &query, const CandidateSet &cs) {
/* (1) Find out root vertex */
int root = 0;
float min_value = 100.0;
// Find vertex who has minimum value of CS_ini(v)/degree(v) and set as root.
for (int i = 0; i < query.GetNumVertices(); i++) {
float value = (float)cs.GetCandidateSize(i) / (float)query.GetDegree(i);
if (value < min_value) {
root = i;
min_value = value;
}
}


/* (2) Put undirected query graph Q to DAG vertor. */
std::vector<std::vector<int>> DAG;
DAG.resize(query.GetNumVertices());
// For all vertexes in query graph, find vertexes who have edge with current vertex then put it to DAG[current vertex] vector.
for (int i = 0; i < query.GetNumVertices(); i++) {
for (int offset = query.GetNeighborStartOffset(i); offset < query.GetNeighborEndOffset(i); offset++) {
DAG[i].push_back(query.GetNeighbor(offset));
}
}


/* (3) Do BFS to get order vector needed transfer DAG vertex to directed one. */
std::vector<int> order;
// Save BFS order starting from root to order vector
BFS(order, root, query);


/* (4) Make DAG to real DAG */
buildDAG(DAG, order, 0);


/* (5) Find out all possible matching order */
std::vector<std::vector<int>> match_order;
get_match_order(data, query, cs, DAG, match_order, root);


/* (6) Open file to write down */

// M means partial embedding path of data graph G matching with query DAG.
std::vector<int> M;

if (writeFile.is_open()) {
writeFile << "t " << query.GetNumVertices() << "\n";
}


/* (7) Backtrack based on matching order and find all complete embeddings */
backtrack(data, query, cs, match_order, M, 0);
}
