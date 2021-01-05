#include <iostream>
#include <fstream>
#include <string>
#include <cassert>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <cstdlib>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
#include <openssl/bn.h>
#include <time.h>
#include <stdlib.h>
// All the header file about NS-3
#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/internet-module.h"
#include "ns3/point-to-point-module.h"
#include "ns3/applications-module.h"
#include "ns3/virtual-net-device.h"
#include "ns3/ipv4-global-routing-helper.h"
#include "ns3/ipv4-static-routing-helper.h"
#include "ns3/packet-sink.h"
#include "ns3/nstime.h"
#include "ns3/v4ping-helper.h"
#include "ns3/traffic-control-module.h"
// For monitor the TCP flow
#include "ns3/flow-monitor.h"
#include "ns3/flow-monitor-helper.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/trace-helper.h"
/****************************** macro *************************************************/
#define random(x) (rand()%x)
#define MAX_LINKNUM 9
#define INIT_INDEX 128
#define MAX_GROUP_LEN 100
#define FILE_NAME "BMP" 
NS_LOG_COMPONENT_DEFINE("BMP_CUBIC");
/****************************** name space ********************************************/
using namespace std;
using namespace ns3;
/***************************** struct defination **************************************/
struct thdr //16字节
{
	uint32_t 	g_packetindex;                            // gobal packet index
	uint32_t	p_packetindex;	                          // packet index of network adapter
	uint8_t     SMR_serial_number;
	uint8_t     SAR_serial_number : 4;			// group length M
	uint8_t     Adapter_serial_number : 4;
	uint8_t     Alogrithm_serial_number : 4;
	uint8_t     header_len : 4;     // header lenght
	uint8_t     algorithm_K : 4;
	uint8_t     algorithm_N : 4;
	uint8_t     algorithm_en_seq;
	uint8_t     algorithm_gq_seq[3]; //这是啥 ycy
};
struct pac_info
{
	Ptr<Packet> pac;
	uint64_t    time;
	uint32_t	queue_len;      // Network adapter send queue lenght
	uint32_t    total_data;     // The amount of data sent by the network card
	uint32_t 	g_packetindex;  // gobal packet index
	uint32_t	p_packetindex;	// packet index of network adapter
	uint32_t    packet_len;
	uint32_t     ppp_index;
	uint32_t     algorithm_K;
	uint32_t     algorithm_N;
	uint32_t     algorithm_en_seq;
	uint32_t    algorithm_gq_seq;
	uint32_t    expect_group;
};
struct link_info
{
	uint64_t    last_time;
	uint64_t    current_time;
	double rate;
	double loss;
	double delay;
	double queue;
	double jitter;
	double ratio;
	uint32_t used;
	uint32_t k;
	uint32_t n;
};
struct RecvPacket
{
	pac_info info;
	uint8_t src[2048];
};
struct RecvGroup
{
	map<uint32_t,struct RecvPacket> group;
	uint32_t n;
	uint32_t k;
	uint32_t sent_num;
};

struct group_info
{
	uint32_t group_index;
	uint32_t algorithm_K;
	uint32_t algorithm_N;
	uint32_t recv_num;
};



uint8_t EM[7][16][7] = {
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [0][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } }, 
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [1][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } },
	{ { 0, 0, 0, 0, 1, 0, 0 },	// [2][0]
	{ 0, 0, 0, 0, 0, 1, 0 },
	{ 0, 0, 0, 0, 0, 0, 1 },
	{ 0, 0, 0, 0, 1, 2, 3 },
	{ 0, 0, 0, 0, 3, 1, 2 },
	{ 0, 0, 0, 0, 2, 3, 1 },
	{ 0, 0, 0, 0, 1, 4, 9 },
	{ 0, 0, 0, 0, 9, 1, 4 },
	{ 0, 0, 0, 0, 4, 9, 1 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } },
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [3][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } },
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [4][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } },
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [5][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } },
	{ { 0, 0, 0, 0, 0, 0, 0 },	// [6][0]
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 },
	{ 0, 0, 0, 0, 0, 0, 0 } }
};


struct Info_Abstract
{
    string file;
    string time;
    double link_bw[3];
    double link_loss[3];
    double link_delay[3];
    double TCP_bw;
    double TCP_max_bw;
    double TCP_loss;
    double TCP_delay;
    double TCP_tx_packets;
    double TCP_rx_packets;
    double real_tx_packets[3];
    double real_rx_packets[3];
    double real_link_bw[3];
    double real_link_loss[3];
    double real_link_delay[3];
};
