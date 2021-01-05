/**************************************************************************************
This is the Network Coding multipath transmission source file, which is changed by base
multipath trasmission file BMP.cc.
***************************************************************************************/

/**************************** head file list*******************************************/

// All the header file about C++ 
#include "Standard_NC_v1.0.h"

string VERSION; 
int FILE_PRINT = 1;
int PCAP = 1;
int FILE_ABSTRACT = 1; 
int FILE_MULTI_SEND = 1;
int FILE_MULTI_RECV = 1;
int FILE_REAL_RECV = 1;
int FILE_REAL_RATE = 1;
int FILE_SINGLE = 1;

int SCREEN_REAL_RATE = 1;
int SCREEN_ABSTRACT = 1;

ofstream file_abstrct;
ofstream file_multi_send;
ofstream file_multi_recv;
ofstream file_real_recv;
ofstream file_real_rate;


vector<struct Info_Abstract> Task_Abstract;
/***************************** global variable **************************************/
int LINKNUM = 3;

int FeedbackInfoLen = 20;
int FeedbackOverlap = 10;
//int MaxRecordGroupLen = 100;

double real_link_delay[3]={0,0,0};

/* Detect if the output is to a new file that needs a header or not. */


/**/
ofstream out_32;
ofstream out_task;
ofstream out_seq;
ofstream out_para;
const double eps = 1e-6;
float globledelay[3]={0,0,0};
//float globletime[3]={0,0,0};
uint32_t globlenum[3]={0,0,0};
vector<float> timeset;
/* dynamic change link bandwidth*/
vector<string> mylist={
"2Mbps",
"3Mbps",
"2.5Mbps",
"3.5Mbps",
"1.4Mbps",
"4.5Mbps",
"3.1Mbps",
"6.9Mbps",
"10.1Mbps",
"1Mbps",
"0.5Mbps",
"0.7Mbps",
"6.1Mbps",
"1.5Mbps",
"2.4Mbps",
"1.3Mbps",
"1.2Mbps",
"1Mbps"};
void BandwidthTrace (void);
void ScheduleBw (void);
//string bandwidth = "15Mbps";
uint32_t m_timer_value = 500;

int i=0;
void
BandwidthTrace (void)
{
        //string myBandwidth;
        int index=rand()%10;
        //cout<<index<<endl;
        cout << "set  bandwidth: " << mylist[index]<< endl;
        Config::Set ("/NodeList/*/DeviceList/*/PointToPointNetDevice/DataRate",StringValue ("0.0001"));
        //cout << "ok" << endl;
        if (i!=14)
        {
                ScheduleBw ();
                i=+1;
        }
        else
        {
                //cout << "end of file!" << endl;
        }

}

void
ScheduleBw (void)
{
        Simulator::Schedule (MilliSeconds (m_timer_value), BandwidthTrace);
}
/***************************** global function **************************************/
 // 求矩阵的行列式
int detA(double *OrigA, int dimA) 
{
	int i, j, k, n;
	double ans = 0;
	n = dimA;
	if (n == 1)
	{
		return OrigA[0];
	}
	double *temp = (double *)calloc((dimA - 1) * (dimA - 1), sizeof(double));
	for (i = 0; i < n; i++)
	{
		for (j = 0; j < n - 1; j++)
		{
			for (k = 0; k < n - 1; k++)
			{
				temp[j * (dimA - 1) + k] = OrigA[(j + 1) * dimA + (k >= i ? k + 1 : k)];
			}
		}
		double t = detA(temp, n - 1);
		if (i % 2 == 0)
		{
			ans += OrigA[i] * t;
		}
		else
		{
			ans -= OrigA[i] * t;
		}
	}
	free(temp);
	return ans;
}

int round_double(double number)
{
	return (number > 0.0) ? (number + 0.5) : (number - 0.5);
}
//矩阵乘法
void mul(vector<double>& A, vector<double>&B, vector<double>& C, int dim, int index)
{
	for (int i = 0; i<dim; i++)
	{
		for (int j = 0; j<dim; j++)
		{
			for (int k = 0; k<dim; k++)
			{
				C[i*dim + j] += A[i*dim + k] * B[k*dim + j] * index;
			}
		}
	}

	//若绝对值小于10^-10,则置为0（这是我自己定的）
	for (int i = 0; i<dim*dim; i++)
	{
		if (abs(C[i])<pow(10, -10))
		{
			C[i] = 0;
		}
	}
}

//LUP分解
void LUP_Descomposition(vector<double>& A, vector<double>& L, vector<double>& U, vector<int>& P, int dim)
{
	int row = 0;
	for (int i = 0; i<dim; i++)
	{
		P[i] = i;
	}
	for (int i = 0; i<dim - 1; i++)
	{
		double p = 0.0;
		for (int j = i; j<dim; j++)
		{
			if (abs(A[j*dim + i])>p)
			{
				p = abs(A[j*dim + i]);
				row = j;
			}
		}
		if (0 == p)
		{
			std::cout << "矩阵奇异，无法计算逆" << endl;
			return;
		}

		//交换P[i]和P[row]
		int tmp = P[i];
		P[i] = P[row];
		P[row] = tmp;

		double tmp2 = 0.0;
		for (int j = 0; j<dim; j++)
		{
			//交换A[i][j]和 A[row][j]
			tmp2 = A[i*dim + j];
			A[i*dim + j] = A[row*dim + j];
			A[row*dim + j] = tmp2;
		}

		//以下同LU分解
		double u = A[i*dim + i], l = 0.0;
		for (int j = i + 1; j<dim; j++)
		{
			l = A[j*dim + i] / u;
			A[j*dim + i] = l;
			for (int k = i + 1; k<dim; k++)
			{
				A[j*dim + k] = A[j*dim + k] - A[i*dim + k] * l;
			}
		}

	}

	//构造L和U
	for (int i = 0; i<dim; i++)
	{
		for (int j = 0; j <= i; j++)
		{
			if (i != j)
			{
				L[i*dim + j] = A[i*dim + j];
			}
			else
			{
				L[i*dim + j] = 1;
			}
		}
		for (int k = i; k<dim; k++)
		{
			U[i*dim + k] = A[i*dim + k];
		}
	}
	return;
}

//LUP求解方程
void LUP_Solve(vector<double>& L, vector<double>& U, vector<int>& P, vector<double>& b, vector<double>& x, int dim)
{
	vector<double>y;
	y.resize(dim);
	//正向替换
	for (int i = 0; i < dim; i++)
	{
		y[i] = b[P[i]];
		for (int j = 0; j < i; j++)
		{
			y[i] = y[i] - L[i*dim + j] * y[j];
		}
	}
	//反向替换
	for (int i = dim - 1; i >= 0; i--)
	{
		x[i] = y[i];
		for (int j = dim - 1; j > i; j--)
		{
			x[i] = x[i] - U[i*dim + j] * x[j];
		}
		x[i] /= U[i*dim + i];
	}
}

/*****************矩阵原地转置BEGIN********************/
/* 后继 */
int getNext(int i, int m, int dim)
{
	return (i%dim)*m + i / dim;
}
/* 前驱 */
int getPre(int i, int m, int dim)
{
	return (i%m)*dim + i / m;
}

/* 处理以下标i为起点的环 */
void movedata(vector<double>& mtx, int i, int m, int dim)
{
	double temp = mtx[i]; // 暂存
	int cur = i;    // 当前下标
	int pre = getPre(cur, m, dim);
	while (pre != i)
	{
		mtx[cur] = mtx[pre];
		cur = pre;
		pre = getPre(cur, m, dim);
	}
	mtx[cur] = temp;
}

/* 转置，即循环处理所有环 */
void transpose(vector<double>& mtx, int m, int dim)
{
	for (int i = 0; i<m*dim; ++i)
	{
		int next = getNext(i, m, dim);
		while (next > i) // 若存在后继小于i说明重复,就不进行下去了（只有不重复时进入while循环）
			next = getNext(next, m, dim);
		if (next == i)  // 处理当前环
			movedata(mtx, i, m, dim);
	}
}
/*****************矩阵原地转置END********************/

//LUP求逆(将每列b求出的各列x进行组装)
void LUP_solve_inverse(vector<double>& A, vector<double>& inv_A, int coefficient, int dim)
{
	//创建矩阵A的副本，注意不能直接用A计算，因为LUP分解算法已将其改变
	vector<double> A_mirror = A;
	//double *inv_A = new double[dim*dim]();//最终的逆矩阵（还需要转置）
	//	vector<double> inv_A;
	//	inv_A.resize(dim*dim);
	//矩阵逆的各列
	vector<double> inv_A_each;
	inv_A_each.resize(dim);
	//b阵为B阵的列矩阵分量
	vector<double> b;
	b.resize(dim);

	for (int i = 0; i<dim; i++)
	{
		vector<double> L;
		L.resize(dim*dim);
		vector<double> U;
		U.resize(dim*dim);
		vector<int> P;
		P.resize(dim);

		//构造单位阵的每一列
		for (int i = 0; i<dim; i++)
		{
			b[i] = 0;
		}
		b[i] = 1;

		//每次都需要重新将A复制一份
		for (int i = 0; i<dim*dim; i++)
		{
			A_mirror[i] = A[i];
		}

		LUP_Descomposition(A_mirror, L, U, P, dim);

		LUP_Solve(L, U, P, b, inv_A_each, dim);
		inv_A.insert(inv_A.end(), inv_A_each.begin(), inv_A_each.end());
		//memcpy(inv_A + i*dim, inv_A_each, dim*sizeof(double));//将各列拼接起来
	}
	transpose(inv_A, dim, dim);//由于现在根据每列b算出的x按行存储，因此需转置

	//return inv_A;
}

class MyApp : public Application
{
public:
	MyApp();
	virtual ~MyApp();
	/**
	* Setup the example application.
	*/
	void Setup(Ptr<Socket> socket, Address address, uint32_t packetSize, uint32_t nPackets, DataRate dataRate);
private:
	virtual void StartApplication(void);
	virtual void StopApplication(void);
	void ScheduleTx(void);
	void SendPacket(void);

	Ptr<Socket>     m_socket;
	Address         m_peer;
	uint32_t        m_packetSize;
	uint32_t        m_nPackets;
	DataRate        m_dataRate;
	EventId         m_sendEvent;
	bool            m_running;
	uint32_t        m_packetsSent;

};

MyApp::MyApp()
	: m_socket(0),
	m_peer(),
	m_packetSize(0),
	m_nPackets(0),
	m_dataRate(0),
	m_sendEvent(),
	m_running(false),
	m_packetsSent(0)
{
}

MyApp::~MyApp()
{
	m_socket = 0;
}

/**
* Setup the application.
* Parameters:
* socket     Socket to send data to.
* address    Address to send data to.
* packetSize Size of the packets to send.
* nPackets   Number of packets to send.
* dataRate   Data rate used to determine when to send the packets.
*/
void MyApp::Setup(Ptr<Socket> socket, Address address, uint32_t packetSize, uint32_t nPackets, DataRate dataRate)
{
	m_socket = socket;
	m_peer = address;
	m_packetSize = packetSize;
	m_nPackets = nPackets;
	m_dataRate = dataRate;
}

/**
* Start sending data to the address given in the Setup method.
*/
void MyApp::StartApplication(void)
{
	m_running = true;
	m_packetsSent = 0;
	m_socket->Bind();
	m_socket->Connect(m_peer);
	SendPacket();
}

/**
* Stop sending data to the address given in the Setup method.
*/
void MyApp::StopApplication(void)
{
	m_running = false;

	if (m_sendEvent.IsRunning())
	{
		Simulator::Cancel(m_sendEvent);
	}

	if (m_socket)
	{
		m_socket->Close();
	}
}

/**
* Send a packet to the receiver.
*/
void MyApp::SendPacket(void)
{
	Ptr<Packet> packet = Create<Packet>(m_packetSize);
	m_socket->Send(packet);

	if (++m_packetsSent < m_nPackets)
	{
		ScheduleTx();
	}
	else
	{
		std::cout << "Done sending packets: " << m_packetsSent;
	}
}

/**
* Schedule when the next packet will be sent.
*/
void MyApp::ScheduleTx(void)
{
	if (m_running)
	{
		Time tNext(Seconds(m_packetSize * 8 / static_cast<double> (m_dataRate.GetBitRate())));
		//NS_LOG_INFO("Send next packet at: " << tNext);
		m_sendEvent = Simulator::Schedule(tNext, &MyApp::SendPacket, this);
	}
}


void PrintPacketInfo(struct pac_info& pac,int index)
{
	file_real_recv << index << '\t'  // 1 为单位矩阵接收，2 为冗余接收，3 为超时单位
		<< pac.g_packetindex << '\t'
		<< pac.p_packetindex << '\t'
		<< (int)pac.ppp_index << '\t'
		<< pac.time << '\t'
		<< pac.total_data << '\t'
		<< pac.queue_len << '\t'
		<< pac.packet_len << '\t'
		<< (uint32_t)pac.algorithm_K << '\t'
		<< (uint32_t)pac.algorithm_N << '\t'
		<< (uint32_t)pac.algorithm_en_seq << '\t'
		<< (uint32_t)pac.algorithm_gq_seq << '\t'
		<< pac.expect_group
		<<endl;
}
// Link between SMR and SAR
class TLink
{

public:
	// 0 for node A and 1 for node B
	Ipv4Address m_address[2];                  // Node  address
	Ptr<Queue<Packet> > m_txqueue[2];                     // Node A send queue

	vector<struct pac_info*> m_send[2];
	vector<struct pac_info*> m_recv[2];
	uint8_t  ppp_index;                      // link index;
	NetDeviceContainer deviceContainer;     // device container
	Ipv4InterfaceContainer interfaceContainer;  // 
	double set_loss;                        // Loss rate of link set 
	double set_bandwidth;                   // Bandwidth of link set
	double set_rtt;                         // RTT of link set

	uint8_t file_path[512];                 // File save path

public:
	TLink();
	TLink(int index, double loss, double bandwidth, double rtt);
	void CreateP2PLink(NodeContainer &n0n1,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3);
	void PrintLinkInfo(int index,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3);

};
TLink::TLink()
{
	ppp_index = 0;
	set_loss = 0;
	set_bandwidth = 0;
	set_rtt = 0;
	//file_path = "";
}
TLink::TLink(int index, double loss, double bandwidth, double rtt)
{
	ppp_index = index;
	set_loss = loss;
	set_bandwidth = bandwidth;
	set_rtt = rtt;
	//file_path = "";
        //DatRate1=DataRate1;
        //DataRate2=DataRate2;
        //DataRate3=DataRate3,
        //Delay1=Delay1;
        //Delay2= Delay2;
        //Delay3=Delay3;
        //Loss1=Loss1;
        //Loss2=Loss2;
        //Loss3=Loss3;
}
// 初始化链路
void TLink::CreateP2PLink(NodeContainer &n0n1,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3)
{
	// set bandwidth
	PointToPointHelper p2p;
	p2p.SetQueue("ns3::DropTailQueue");//Each point to point net device must have a queue to pass packets through. This method allows one to set the type of the queue that is automatically created when the device is created and attached to a node.
	//std::ostringstream oss;
	//oss << set_bandwidth << "Mbps";
        switch(this->ppp_index)
        {
        case 0 :{
	std::ostringstream oss1;
	oss1 << DataRate1 << "Mbps";
        p2p.SetDeviceAttribute("DataRate", StringValue(oss1.str()));
        break;}
        case 1 :{
	std::ostringstream oss2;
	oss2 << DataRate2 << "Mbps";
        p2p.SetDeviceAttribute("DataRate", StringValue(oss2.str()));
        break;}
        case 2 :{
	std::ostringstream oss3;
	oss3 << DataRate3 << "Mbps";
        p2p.SetDeviceAttribute("DataRate", StringValue(oss3.str()));
        break;}
        default:{
            std::ostringstream oss4;
            oss4 << this->set_bandwidth << "Mbps";
            p2p.SetDeviceAttribute("DataRate", StringValue(oss4.str()));
            break;
         }
        }
        //p2p.SetDeviceAttribute("DataRate", StringValue(oss.c_str()));
	// set delay
        switch(this->ppp_index)
        {
        case 0 :{
        p2p.SetChannelAttribute("Delay", TimeValue(MilliSeconds(Delay1)));
        break;}
        case 1 :{
        p2p.SetChannelAttribute("Delay", TimeValue(MilliSeconds(Delay2)));
        break;}
        case 2 :{
        p2p.SetChannelAttribute("Delay", TimeValue(MilliSeconds(Delay3)));
        break;}
        default:{
            p2p.SetChannelAttribute("Delay", TimeValue(MilliSeconds(set_rtt)));
            break;
         }
        }
	//p2p.SetChannelAttribute("Delay", TimeValue(MilliSeconds(set_rtt)));
	deviceContainer = p2p.Install(n0n1);
	//NetDeviceContainer ns3::PointToPointHelper::Install(NodeContainer c)	

        // set loss rate 
        switch(this->ppp_index)
        {
        case 0 :{
	Ptr<RateErrorModel> errorModel1 = CreateObject<RateErrorModel>();
	errorModel1->SetAttribute("ErrorUnit", EnumValue(2));
	errorModel1->SetAttribute("ErrorRate", DoubleValue(Loss1));
        deviceContainer.Get(1)->SetAttribute("ReceiveErrorModel", PointerValue(errorModel1));
        break;}
        case 1 :{
	Ptr<RateErrorModel> errorModel2 = CreateObject<RateErrorModel>();
	errorModel2->SetAttribute("ErrorUnit", EnumValue(2));
	errorModel2->SetAttribute("ErrorRate", DoubleValue(Loss2));
        deviceContainer.Get(1)->SetAttribute("ReceiveErrorModel", PointerValue(errorModel2));
        break;}
        case 2 :{
	Ptr<RateErrorModel> errorModel3 = CreateObject<RateErrorModel>();
	errorModel3->SetAttribute("ErrorUnit", EnumValue(2));
	errorModel3->SetAttribute("ErrorRate", DoubleValue(Loss3));
        deviceContainer.Get(1)->SetAttribute("ReceiveErrorModel", PointerValue(errorModel3));
        break;}
        default:{
	Ptr<RateErrorModel> errorModel4 = CreateObject<RateErrorModel>();
	errorModel4->SetAttribute("ErrorUnit", EnumValue(2));
	errorModel4->SetAttribute("ErrorRate", DoubleValue(set_loss));
        deviceContainer.Get(1)->SetAttribute("ReceiveErrorModel", PointerValue(errorModel4));
            break;
         }
        }
	//Ptr<RateErrorModel> errorModel = CreateObject<RateErrorModel>();
	//errorModel->SetAttribute("ErrorUnit", EnumValue(2));
	//errorModel->SetAttribute("ErrorRate", DoubleValue(set_loss));
	
        //Ptr<UniformRandomVariable> loss_1 =CreateObject<UniformRandomVariable>();
        //loss_1->SetAttribute ("Min",DoubleValue(0));
        //loss_1->SetAttribute ("Max",DoubleValue(0.001));
	//errorModel->SetAttribute("ErrorRate", DoubleValue(loss_1->GetValue()));
	//errorModel->SetAttribute("ErrorRate", DoubleValue("ns3::UniformRandomVariable[Min=0.0|Max=0.001]"));
	
        //deviceContainer.Get(1)->SetAttribute("ReceiveErrorModel", PointerValue(errorModel));
	//Ptr<NetDevice> ns3::NetDeviceContainer::Get(uint32_t i)const
        //Get the Ptr<NetDevice> stored in this container at a given index.
        // set tx queue
	m_txqueue[0] = DynamicCast<PointToPointNetDevice>(deviceContainer.Get(0))->GetQueue();//Get a copy of the attached Queue.
	m_txqueue[1] = DynamicCast<PointToPointNetDevice>(deviceContainer.Get(1))->GetQueue();
	//Ptr<Queue<Packet>>GetQueue (void) const
        // set address
	Ipv4AddressHelper ipv4;
	char ipaddr_node[20];
	sprintf(ipaddr_node, "10.0.%d.0", int(ppp_index) + 1);
	ipv4.SetBase(ipaddr_node, "255.255.255.0", "0.0.0.1");
	interfaceContainer = ipv4.Assign(deviceContainer);
	m_address[0] = interfaceContainer.GetAddress(0);
	m_address[1] = interfaceContainer.GetAddress(1);
	//p2p.EnablePcapAll("NC_info");
}
void TLink::PrintLinkInfo(int index,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3)
{
	std::ostringstream addrOss[2];
	m_address[0].Print(addrOss[0]);
	m_address[1].Print(addrOss[1]);
	std::cout << "Link : " << (int)ppp_index << std::endl;
	std::cout << "From : " << addrOss[0].str().c_str() << "\t To : " << addrOss[1].str().c_str() << std::endl;
        if(index==0){
	std::cout << "Loss : " << Loss1 << std::endl;
	std::cout << "Bandwidth : " << DataRate1 << std::endl;
	std::cout << "Delay : " << Delay1 << std::endl;
        }
        if(index==1){
        std::cout << "Loss : " << Loss2 << std::endl;
        std::cout << "Bandwidth : " << DataRate2 << std::endl;
        std::cout << "Delay : " << Delay2 << std::endl;
        }
        if(index==2){
        std::cout << "Loss : " << Loss3 << std::endl;
        std::cout << "Bandwidth : " << DataRate3 << std::endl;
        std::cout << "Delay : " << Delay3 << std::endl;
        }

}

/***********************************************************
在这之前的内容基本上不用修改，调试时要修改的内容在后面
************************************************************/

class Tunnel
{
public:
	Tunnel(Ptr<Node> n,
		Mac48Address tunMAC,
		Ipv4Address tunIP,
		vector<TLink*> &link,
		int NodeIndex,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3,int PacketSize);

	~Tunnel();
public:
	Ptr<Queue<Packet> > m_tx[MAX_LINKNUM];
	int m_index;                         // 隧道端点
	Ptr<Socket> m_Socket[MAX_LINKNUM];
	Ipv4Address m_remoteIP[MAX_LINKNUM];
	//Ptr<Socket> m_token_socket;
	//Ipv4Address m_token_remoteIP;
	Ptr<VirtualNetDevice> m_tun;
	
	vector<struct pac_info> m_sendPac;  // 记录发送信息
	vector<struct pac_info> m_recvPac;  // 记录接收信息
    vector<struct pac_info> m_sendIMPac;  // 记录发送信息
    vector<struct pac_info> m_recvIMPac;  // 记录接收信息
	map<uint32_t, struct group_info> m_send_group;  // 对端发送数据包分组冗余情况
	map<uint32_t, struct group_info> m_recv_group;
	map<uint32_t, double> m_recv_goodput;       // 记录通过32号信令发送的速率
	vector<double> total_recv_goodput;                 // 记录实际到达吞吐量，单位 bit/s
    uint64_t m_timeThreshold;
	int ppp_sendRate[3];
    int m_k;  // 未来要动态调整
    int m_n;
    vector<TLink*> m_link;
    double DataRate[3];
    double Delay[3];
    double Loss[3];
    int PacketSize;
private:
	// 发送端变量
	uint32_t m_g_packetindex;
	uint32_t m_groupindex;
	uint32_t m_p_packetindex[MAX_LINKNUM];
	uint32_t m_total_send[MAX_LINKNUM]; // 某网卡累计发送流量
	vector <Ptr<Packet> > m_sendBuffer;
	
	// 接收端变量
	uint32_t m_total_recv[MAX_LINKNUM]; // 某网卡累计接收流量	
	set<uint32_t> m_dupBuffer;  // 去重缓存
	std::map<uint32_t, struct RecvGroup> m_recvBuffer;  // 接收缓存
	std::set <uint32_t> m_recvFull;
	map<uint32_t,uint64_t> m_lastArrive;
	uint64_t m_lArrive;
	uint32_t m_expectGroup;
	uint64_t m_recv_time;
	uint32_t m_pac_num;
	uint32_t m_pac_size;
public:
	bool AddSendPacInfo(Ptr<Packet> pac, uint32_t ppp, uint32_t en_seq);
	bool AddRecvPacInfo(Ptr<Packet> packet);
    bool AddSendIMPacInfo(Ptr<Packet> pac, uint32_t ppp, uint32_t en_seq);
    bool AddRecvIMPacInfo(Ptr<Packet> packet);
	void PrintAllInfo(ofstream& file,vector<struct pac_info>& data);  // 打印到文件
	
    // 统计信息，统计链路状态
	struct link_info m_send_linkinfo[MAX_LINKNUM];
	struct link_info m_recv_linkinfo[MAX_LINKNUM];
	void GetSendLinkInfo(struct link_info &last, struct link_info &current, uint32_t ppp);
	void GetRecvLinkInfo(struct link_info &last, struct link_info &current);
	int AddGroupInfoBuffer(struct pac_info& packet_info);
private:
	void InitTunnel();
	void GetPacketInfo(uint8_t* src, pac_info& pac);
	void SetPacketInfo(uint8_t* src, pac_info& pac);

	// 发送端函数
	// Receive packets from tunnel
	bool TunSend(Ptr<Packet> packet, const Address& source, const Address& dest, uint16_t protocolNumber);
	// This function determines which Network Adapter the packet is sent from.
	uint32_t SetSendPPP(uint32_t index);
	uint32_t EDPF(uint32_t index);
	uint32_t EDPF_2(uint32_t index);
        uint32_t RR(uint32_t index);
        uint32_t WRR(uint32_t);
        void UpdateGropInfo();
	int Add2SendBuffer(Ptr<Packet> packet);
	Ptr<Packet> SendByIM(uint32_t index, uint32_t ppp);
	Ptr<Packet> SendByRM(uint32_t index, uint32_t ppp, BIGNUM** raw_bn);
	// 接收端函数
	// Receiver packets from network adapter
	void SocketRecv(Ptr<Socket> socket);
	void PacketClassification(Ptr<Packet> old_packet);
	int duplicate(struct pac_info& packet_info);
	int Add2RecvBuffer(uint8_t* src, struct pac_info& packet_info);
	int isExpect(struct pac_info& pac);
	int PacketDecoding(struct pac_info& pac);
	int RegularPacket(std::map<uint32_t, struct RecvGroup>::iterator target,uint32_t index,uint64_t lasttime);
	int TimeoutPacket(std::map<uint32_t, struct RecvGroup>::iterator target,uint32_t index,uint64_t lasttime);
	int ReceiveIM(map<uint32_t, struct RecvPacket>::iterator it,uint32_t index,uint64_t lasttime);
	int ReceiveRM(std::map<uint32_t, struct RecvGroup>::iterator target,int flag,uint32_t index,uint64_t lasttime);
	void CalculateGoodput(uint32_t len,uint32_t index,uint32_t lasttime);
	//Ptr<Packet> CreateGroupInfoPacket();
	//int SendGroupInfoBuffer();
	int Process_32(uint8_t* src, uint32_t len);
};
Tunnel::~Tunnel()
{
}

Tunnel::Tunnel(Ptr<Node> n,
	Mac48Address tunMAC,
	Ipv4Address tunIP,
	vector<TLink*> &link,
	int NodeIndex,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3,int PacketSize)
{       
        DataRate[0]=DataRate1;
        DataRate[1]=DataRate2;
        DataRate[2]=DataRate3,
        Delay[0]=Delay1;
        Delay[1]=Delay2;
        Delay[2]=Delay3;
        Loss[0]=Loss1;
        Loss[1]=Loss2;
        Loss[2]=Loss3;
        PacketSize=PacketSize;

        m_link = link;
	m_index = NodeIndex;
	for (int i = 0; i < LINKNUM; i++) // 建立传输链路
	{
		// Establish a transparent tunnel with UDP
		m_Socket[i] = Socket::CreateSocket(n, TypeId::LookupByName("ns3::UdpSocketFactory"));
		m_Socket[i]->Bind(InetSocketAddress(link[i]->m_address[0 ^ m_index], 555));
		m_Socket[i]->SetRecvCallback(MakeCallback(&Tunnel::SocketRecv, this));
		m_remoteIP[i] = link[i]->m_address[1 ^ m_index];
	}
	//token  建立信令链路
	//m_token_socket = Socket::CreateSocket(n, TypeId::LookupByName("ns3::UdpSocketFactory"));
	//m_token_socket->Bind(InetSocketAddress(link[LINKNUM]->m_address[0 ^ m_index], 555));
	//m_token_socket->SetRecvCallback(MakeCallback(&Tunnel::SocketRecv, this));
	//m_token_remoteIP = link[LINKNUM]->m_address[1 ^ m_index];

	m_tun = CreateObject<VirtualNetDevice>();
	m_tun->SetAddress(tunMAC);
	m_tun->SetSendCallback(MakeCallback(&Tunnel::TunSend, this));
	n->AddDevice(m_tun);
	Ptr<Ipv4> ipv4 = n->GetObject<Ipv4>();
	uint32_t it = ipv4->AddInterface(m_tun);
	ipv4->AddAddress(it, Ipv4InterfaceAddress(tunIP, Ipv4Mask("255.255.255.0")));
	ipv4->SetUp(it);
	for (int i = 0; i < LINKNUM; i++)
	{
		m_tx[i] = link[i]->m_txqueue[0 ^ m_index];
	}
	InitTunnel();
}
// 初始化隧道变量
void Tunnel::InitTunnel()
{
	// 发送端变量
	m_g_packetindex = INIT_INDEX; // 小于INIT_INDEX的是控制信令
    m_groupindex = 0;
	for (int i = 0; i < MAX_LINKNUM; i++)
	{
		m_p_packetindex[i] = 0;
		m_total_send[i] = 0;
		m_total_recv[i] = 0;
	}
	m_k = 3;
	m_n = 5;
	// 接收端变量
	
	m_expectGroup = 1; // 还要再斟酌
	//m_timeThreshold = 40 * 1000;   // 100ms
	m_lArrive = Simulator::Now().GetMicroSeconds();
	m_recv_time = Simulator::Now().GetMicroSeconds();
	m_pac_num = 0;
	m_pac_size = 0;
	total_recv_goodput.push_back(0);
}
// 决定不同的调度算法
uint32_t Tunnel::SetSendPPP(uint32_t index)
{
 uint32_t seq=WRR(index);
 return seq;
 //return 1;
}
uint32_t Tunnel::RR(uint32_t index){
//RR
//m_g_packetindex
     uint32_t temp = index%3;
     return temp;
}
uint32_t Tunnel::EDPF(uint32_t index){
	// EDPF choose min_index=0 when rtt bandwidth and queue length are the same for three links
    double use_time[3];
    for(int i =0;i<3;i++)
    {
        use_time[i] = m_link[i]->set_rtt + m_tx[i]->GetNBytes()*8 / m_link[i]->set_bandwidth / 1000;
    }
    double min_value = 1e9;
    uint32_t min_index = 0;
    for(int i = 0;i<3;i++)
    {
        if(min_value >use_time[i])
        {
            min_value = use_time[i];
            min_index = i;
        }
    }
    return min_index;
}
uint32_t Tunnel::EDPF_2(uint32_t index){
        // EDPF
    double use_time[3];
    uint32_t min_index;
    for(int i =0;i<3;i++)
    {
        //use_time[i] = m_link[i]->set_rtt + m_tx[i]->GetNBytes()*8 / m_link[i]->set_bandwidth / 1000;
        use_time[i] = (Delay[i]/2 + (PacketSize*8)/(DataRate[i]*1000*1000)+ Loss[i]);
        //std::cout<<i<<":"<<use_time[i]<<std::endl;
        //std::cout<<i<<":"<<m_tx[i]->GetNBytes()*8<<std::endl;
    }
    double min_value = 10000;
    srand((int)index);
    double j=rand()%100/(double)101;
    //cout<<j<<endl;
    if( j < 0.3333){
       min_index=0;
    }else{
      if(j< 0.6666){
        min_index=1;
    }else{
      min_index=2;
    }
    }
    int flag=0;
    uint32_t temp=0;
    for(int i = 0;i<3;i++)
    {
        if(min_value >use_time[i])
        {
            min_value = use_time[i];
            temp = i;
        }
    }
    if(use_time[0]==use_time[1]){flag=1;} 
    if(use_time[1]==use_time[2]){flag=1;} 
    if(use_time[2]==use_time[1]){flag=1;} 
    if(flag==1){
       return min_index;
    }
    return temp;
}

uint32_t Tunnel::WRR(uint32_t index)
{  //WRR
   double use_time[3];
    for(int i =0;i<3;i++)
    {
        use_time[i] = (Delay[i]/2 + (PacketSize*8)/(DataRate[i]*1000*1000))+Loss[i];
    }
    double max_value = 0;
    //uint32_t max_index = 0;
    for(int i = 0;i<3;i++)
    {
        if(max_value < use_time[i])
        {
            max_value = use_time[i];
            //max_index = i;
        }
    }
    double proportion[3];
    for(int i =0;i < 3; i++){
       proportion[i]=max_value/use_time[i];	
    }
    double sum=proportion[0]+proportion[1]+proportion[2];
    for(int i =0;i < 3; i++){
       proportion[i]=proportion[i]/sum;
    }
    int k=0;
    int temp=0;
    for(int i=0; i<3; i++){
	if(temp < proportion[i]){
	   k=i;
           temp=proportion[i];
	}
    }
    int k1=0;
    int temp1=0;
    for(int i=0; i<3; i++){
        if(i!= k){
	if(temp1 < proportion[i]){
	   k1=i;
           temp1=proportion[i];
	}
      }
    }
    int k2=0;
    for(int i=0; i<3; i++){
        if(i!= k && i!=k1 ){
	   k2=i;
	}
      }
    //map<int,double>mapProportion;
    srand((int)time(0));
    double j=rand()%100/(double)101; 
    if( j < proportion[k]){
       return k;
    }else{
      if(j<(proportion[k]+proportion[k1])){
        return k1;
    }else{
      return k2;
    }
    }
}
// 更新分组，决定冗余比例
void Tunnel::UpdateGropInfo()
{
	m_groupindex++;
}
void Tunnel::GetSendLinkInfo(struct link_info &last, struct link_info &current,uint32_t ppp)
{// 这个函数没有完成
	current.last_time = last.current_time;
	current.current_time = Simulator::Now().GetMicroSeconds();
	current.used = m_total_send[ppp];
	current.rate = (current.used - last.used) / (current.current_time - current.last_time);
	
	return;
}
void Tunnel::GetRecvLinkInfo(struct link_info &last, struct link_info &current)
{// 这个函数没有完成
	return;
}
bool Tunnel::AddSendPacInfo(Ptr<Packet> pac, uint32_t ppp, uint32_t en_seq)
{
	struct pac_info pacinfo;
	pacinfo.pac = pac;
	pacinfo.time = Simulator::Now().GetMicroSeconds();
	pacinfo.queue_len = m_tx[ppp]->GetNBytes();
	pacinfo.total_data = m_total_send[ppp];
	pacinfo.g_packetindex = m_g_packetindex;
	pacinfo.p_packetindex = m_p_packetindex[ppp];
	pacinfo.packet_len = pac->GetSize();
	pacinfo.ppp_index = ppp;
	pacinfo.algorithm_K = m_k;
	pacinfo.algorithm_N = m_n;
	pacinfo.algorithm_en_seq = en_seq;
	pacinfo.algorithm_gq_seq = m_groupindex;
	m_sendPac.push_back(pacinfo);
	return 1;
}
bool Tunnel::AddSendIMPacInfo(Ptr<Packet> pac, uint32_t ppp, uint32_t en_seq)
{
        struct pac_info pacinfo;
        pacinfo.pac = pac;
        pacinfo.time = Simulator::Now().GetMicroSeconds();
        pacinfo.queue_len = m_tx[ppp]->GetNBytes();
        pacinfo.total_data = m_total_send[ppp];
        pacinfo.g_packetindex = m_g_packetindex;
        pacinfo.p_packetindex = m_p_packetindex[ppp];
        pacinfo.packet_len = pac->GetSize();
        pacinfo.ppp_index = ppp;
        pacinfo.algorithm_K = m_k;
        pacinfo.algorithm_N = m_n;
        pacinfo.algorithm_en_seq = en_seq;
        pacinfo.algorithm_gq_seq = m_groupindex;
        m_sendIMPac.push_back(pacinfo);
        return 1;
}
bool Tunnel::TunSend(Ptr<Packet> packet, const Address& source, const Address& dest, uint16_t protocolNumber)
{
	Ptr<Packet> new_packet;                                                                  // 待发送数据包
	uint32_t ppp;                                                                            // 选择发送网卡
	BIGNUM* raw_bn[7];                                                                       // 原始数据包映射成的BIGNUM
	uint8_t rawdata[7][2048];                                                                // 原始数据包内容
	uint32_t rawlen[7];                                                                      // 原始数据包长度
	if (!m_sendBuffer.size())
	{
		UpdateGropInfo();   		                                                                  // 设定冗余度，每组数据包调整一次
	}	
	// 数据包到达，进入缓存
	int res = Add2SendBuffer(packet);
	//ppp = SetSendPPP(m_groupindex);
	if (res == 1)
	{	
		// 使用单位矩阵发送,构造发送数据包			                                                              
		m_g_packetindex++;
		ppp = SetSendPPP(m_g_packetindex);                 // 选择发送网卡
		m_p_packetindex[ppp]++;
		new_packet = SendByIM(m_sendBuffer.size()-1, ppp);             
		m_Socket[ppp]->SendTo(new_packet, 0, InetSocketAddress(m_remoteIP[ppp], 555));        // 发送
		m_total_send[ppp]+=new_packet->GetSize();
		AddSendPacInfo(new_packet, ppp, m_sendBuffer.size() - 1);                             // 添加发送记录
        AddSendIMPacInfo(new_packet, ppp, m_sendBuffer.size() - 1);


	}else
	{
		// 使用单位矩阵发送第K个包,构造发送数据包		
		m_g_packetindex++;
		ppp = SetSendPPP(m_g_packetindex);		                                                              // 选择发送网卡
		m_p_packetindex[ppp]++;
		new_packet = SendByIM(m_sendBuffer.size() - 1, ppp);
		m_Socket[ppp]->SendTo(new_packet, 0, InetSocketAddress(m_remoteIP[ppp], 555));        // 发送
		m_total_send[ppp] += new_packet->GetSize();
		AddSendPacInfo(new_packet, ppp, m_sendBuffer.size() - 1);                             // 添加发送记录
        AddSendIMPacInfo(new_packet, ppp, m_sendBuffer.size() - 1);
		// 获取数据包，将数据包映射成BIGNUM
		for (int k = 0; k < m_k; k++)                                                         // K 循环
		{
			//cout << k * 10 << endl;
			memset(rawdata[k], 0, 2048);
			Ptr<Packet> temp = m_sendBuffer[k];
			rawlen[k] = temp->CopyData(rawdata[k], 2048);
			raw_bn[k] = BN_new();
			BN_bin2bn(rawdata[k], rawlen[k], raw_bn[k]);
		}
		// 使用冗余矩阵发送
		for (int i = 0; i < m_n - m_k; i++)                                                   // N - K 循环
		{
			//cout << i*1000 << endl;	
			m_g_packetindex++;
			ppp = SetSendPPP(m_g_packetindex);
			m_p_packetindex[ppp]++;
			new_packet = SendByRM(i, ppp,raw_bn);
			m_Socket[ppp]->SendTo(new_packet, 0, InetSocketAddress(m_remoteIP[ppp], 555));    // 发送
			m_total_send[ppp] += new_packet->GetSize();
			AddSendPacInfo(new_packet, ppp, m_k + i);                                         // 添加发送记录
		}// end for
		
		m_sendBuffer.clear(); // 清空发送缓存
		for (int i = 0; i < m_k; i++)
		{
	 		BN_free(raw_bn[i]);  // 我觉得这里还是应该清理，内存够用，先不清理
		}
	}// end else
       
	return true;
}
// 数据包到达，首先进入缓存
int Tunnel::Add2SendBuffer(Ptr<Packet> packet)
{
	m_sendBuffer.push_back(packet);
	return m_sendBuffer.size() < m_k;  //这里是小于
}
// 使用单位矩阵发送数据包
Ptr<Packet> Tunnel::SendByIM(uint32_t index, uint32_t ppp)
{
	uint8_t senddata[2048];	
	Ptr<Packet> old_packet = m_sendBuffer[index];
	int hd_len = sizeof(struct thdr);
	int len = old_packet->CopyData(senddata + hd_len, 2048); 
	struct thdr* packet_hdr = (struct thdr*)senddata;
	packet_hdr->g_packetindex = m_g_packetindex;
	packet_hdr->p_packetindex = m_p_packetindex[ppp];
	packet_hdr->SMR_serial_number = Simulator::Now().GetMicroSeconds();          // 这里目前随便填的
	packet_hdr->SAR_serial_number = 0x04;          // 这里目前随便填的
	packet_hdr->Adapter_serial_number = ppp;
	packet_hdr->Alogrithm_serial_number = 0x02; 
	packet_hdr->header_len = (hd_len - 12) / 2;    // 这里填写的内容没有真正使用
	packet_hdr->algorithm_K = m_k;
	packet_hdr->algorithm_N = m_n;
	packet_hdr->algorithm_en_seq = (uint8_t)index;
	memcpy(packet_hdr->algorithm_gq_seq, &m_groupindex, 3);
	Ptr<Packet> new_packet = Create<Packet>(senddata, len + hd_len);
	return new_packet;
}

Ptr<Packet> Tunnel::SendByRM(uint32_t index, uint32_t ppp, BIGNUM** raw_bn)
{
	uint8_t senddata[2048];
	BIGNUM* send_bn;
	int hd_len = sizeof(struct thdr);
	int ec_len = 0;    // 编码后长度
	send_bn = BN_new();
	BN_zero(send_bn); // clear zero
	memset(senddata, 0, sizeof(uint8_t) * 2048);
	for (int k = 0; k < m_k; k++)
	{
		BIGNUM* inner;
		inner = BN_new();

		BN_zero(inner);
		BN_add(inner, inner, raw_bn[k]);
		BN_ULONG coefficient = EM[m_k-1][m_k+index][7-m_k+k];  //暂时先用这个矩阵
		BN_mul_word(inner, coefficient);
		BN_add(send_bn, send_bn, inner);
		BN_free(inner);
	}// end for
	ec_len = BN_bn2bin(send_bn, senddata + hd_len);
	struct thdr* packet_hdr = (struct thdr*)senddata;
	packet_hdr->g_packetindex = m_g_packetindex;
	packet_hdr->p_packetindex = m_p_packetindex[ppp];
	packet_hdr->SMR_serial_number = Simulator::Now().GetMicroSeconds();
	packet_hdr->SAR_serial_number = 0x04;
	packet_hdr->Adapter_serial_number = ppp;
	packet_hdr->Alogrithm_serial_number = 0x02;
	packet_hdr->header_len = (hd_len - 12) / 2;
	packet_hdr->algorithm_K = m_k;
	packet_hdr->algorithm_N = m_n;
	packet_hdr->algorithm_en_seq = (uint8_t)(m_k + index);
	memcpy(packet_hdr->algorithm_gq_seq, &m_groupindex, 3);
	Ptr<Packet> new_packet = Create<Packet>(senddata, ec_len + hd_len);
	BN_free(send_bn);
	return new_packet;
}
bool Tunnel::AddRecvPacInfo(Ptr<Packet> packet)
{
	struct pac_info pacinfo;
	pacinfo.pac = packet;
	uint8_t pdata[2048];
	uint32_t len = packet->CopyData(pdata, 2048);
	pacinfo.packet_len = len;
	pacinfo.pac = packet;
	if (len > sizeof(struct thdr))
	{
		GetPacketInfo(pdata, pacinfo);
		m_total_recv[pacinfo.ppp_index] += len;
		pacinfo.total_data = m_total_recv[pacinfo.ppp_index];
		m_recvPac.push_back(pacinfo);
	}
	return 1;
}
bool Tunnel::AddRecvIMPacInfo(Ptr<Packet> packet)
{
        struct pac_info pacinfo;
        pacinfo.pac = packet;
        uint8_t pdata[2048];
        uint32_t len = packet->CopyData(pdata, 2048);
        pacinfo.packet_len = len;
        m_recvIMPac.push_back(pacinfo);
        return 1;
}
void Tunnel::GetPacketInfo(uint8_t* src, struct pac_info& packet_info)
{
	struct thdr* pac = (struct thdr*)src;
	packet_info.g_packetindex = pac->g_packetindex;
	packet_info.p_packetindex = pac->p_packetindex;
	//packet_info.time = Simulator::Now().GetMicroSeconds();
	packet_info.queue_len = 0;
        packet_info.time = pac->SMR_serial_number;
	
	int ppp = pac->Adapter_serial_number;
	packet_info.ppp_index = ppp;
	packet_info.algorithm_K = pac->algorithm_K;
	packet_info.algorithm_N = pac->algorithm_N;
	packet_info.algorithm_en_seq = pac->algorithm_en_seq;
	memset(&packet_info.algorithm_gq_seq,0,4); // 这里必须先清空一次
	memcpy(&packet_info.algorithm_gq_seq, pac->algorithm_gq_seq, 3);	
	return;
}
void Tunnel::SocketRecv(Ptr<Socket> socket)
{
	// 接收数据包
	Ptr<Packet> packet = socket->Recv(65535, 0);
	
	PacketClassification(packet);  // 转发至tun
	return;
}

void Tunnel::PacketClassification(Ptr<Packet> old_packet)
{
	// 解析数据包
	uint8_t src[2048];
	struct pac_info packet_info;
	uint32_t raw_len = old_packet->CopyData(src, 2048);
	packet_info.packet_len = raw_len;
	GetPacketInfo(src, packet_info);
	if (packet_info.g_packetindex < INIT_INDEX)
	{
		// 处理信令数据包
		switch (packet_info.g_packetindex)
		{
		case 32:
			// 收到分组信息数据包
			Process_32(src,raw_len);  // 处理分组信息数据包
			// 发送分组信息确认数据包，暂时不发送
			break;
		case 33:
			// 收到分组信息确认数据包
			break;
		}
	}
	else
	{
		// 处理普通数据包，
		AddRecvPacInfo(old_packet);  // 记录下到达tun 的所有数据包，globalindex和pppindex可以区分
		if (!duplicate(packet_info))    //第一步检查重复包
		{			
			
			AddGroupInfoBuffer(packet_info);   // 添加分组信息缓存
			//SendGroupInfoBuffer();
			// 没有重复的包可以添加缓存
			if (!Add2RecvBuffer(src, packet_info))
			{
				if (m_index == 1 && out_seq.is_open())
                {
                    string s,s1,s2;
                    s = "\n";
                    out_seq << s;
                }
				// 出现冗余包,可用来统计冗余度，目前在SendGroupInfoBuffer中把冗余度发送出去了
			}else{
				PacketDecoding(packet_info);// 第三步，从缓存中读取数据包,对数据包解码，不管前面收到什么数据包，这里都触发解析
			}
		}else
		{
			// 出现重复包，目前这版本不应该出现
		}
		
		
	} // end if/else
}
int Tunnel::Process_32(uint8_t* src,uint32_t len)
{
	uint32_t point = 0;
	point += sizeof(struct thdr);
	double rate = 0;
	memcpy(&rate, src + point, sizeof(double)); // 读出速率
	point += sizeof(double);
	uint32_t group_num = 0;
	memcpy(&group_num, src + point, sizeof(uint32_t)); // 读出分组个数
	point += sizeof(uint32_t);
	uint32_t index = 0;
	for (int i = 0; i < group_num; i++)
	{
		uint32_t group_index = 0;
		memcpy(&group_index, src + point, sizeof(uint32_t)); // 读出分组序号
		point += sizeof(group_index);

		uint8_t k;
		memcpy(&k, src + point, sizeof(uint8_t)); // 读出k
		point += sizeof(uint8_t);

		uint8_t n;
		memcpy(&n, src + point, sizeof(uint8_t)); // 读出n
		point += sizeof(uint8_t);

		uint8_t recv_num;
		memcpy(&recv_num, src + point, sizeof(uint8_t)); // 读出recv_num
		point += sizeof(uint8_t);

		point += sizeof(uint8_t);  // 空白占位
		struct group_info temp;
		temp.group_index = group_index;
		temp.algorithm_K = k;
		temp.algorithm_N = n;
		temp.recv_num = recv_num;
		auto it = m_recv_group.find(group_index);
		if (it == m_recv_group.end())
		{
			m_recv_group.insert(map<uint32_t, struct group_info>::value_type(group_index, temp));
		}
		else
		{
			it->second.group_index = group_index;
			it->second.algorithm_K = k;
			it->second.algorithm_N = n;
			it->second.recv_num = recv_num;
		}
		index = group_index;
		
	}
	 
	m_recv_goodput.insert(map<uint32_t, double>::value_type(index, rate));
	return 1;
}
int Tunnel::duplicate(struct pac_info& packet_info)
{
	// 这里暂时做最简单的去重，不考虑计算复杂度
	set<uint32_t>::iterator it = m_dupBuffer.find(packet_info.g_packetindex);
	if (it != m_dupBuffer.end())
	{
		cout << "index : " << m_index << "\t" << "Duplicate : " << packet_info.g_packetindex << endl;
		return 1; // duplicate packet
	}
	else
	{
		m_dupBuffer.insert(packet_info.g_packetindex);
		return 0; // accept it 
	}
	// 实际部署的时候还要考虑缓存清除，这里仿真不做处理
}
int Tunnel::Add2RecvBuffer(uint8_t* src, struct pac_info& packet_info)
{
	map<uint32_t, RecvGroup>::iterator it = m_recvBuffer.find(packet_info.algorithm_gq_seq);// 查询该分组是否到达过
	if (it != m_recvBuffer.end())
	{
		// find it!
		if (it->second.group.size() >= it->second.k)
		{
			// 冗余数据包，不用加入缓存
			return 0;
		}else
		{
			// 加入缓存
			RecvPacket temp;
			temp.info = packet_info;
			memcpy(temp.src, src, packet_info.packet_len);
			it->second.group.insert(map<uint32_t, struct RecvPacket>::value_type(packet_info.algorithm_en_seq, temp));
			return 2;
		}// end if/else
	}else
	{
		RecvGroup recv_group;
		RecvPacket temp;
		temp.info = packet_info;
		memcpy(temp.src, src, packet_info.packet_len);
		recv_group.group.insert(map<uint32_t, struct RecvPacket>::value_type(packet_info.algorithm_en_seq, temp));
		recv_group.n = packet_info.algorithm_N;
		recv_group.k = packet_info.algorithm_K;
		recv_group.sent_num = 0;		
		m_recvBuffer.insert(map<uint32_t, RecvGroup>::value_type(packet_info.algorithm_gq_seq, recv_group));
		return 1;
	}// end if/else
	return -1; // 触发不到这里
}
int Tunnel::AddGroupInfoBuffer(struct pac_info& packet_info)   // 处理打印信息的缓存和处理通信信息的缓存分开
{
	uint32_t index = packet_info.algorithm_gq_seq;
	uint32_t K = packet_info.algorithm_K;
	uint32_t N = packet_info.algorithm_N;
	map<uint32_t, struct group_info>::iterator it = m_send_group.find(index);
	if (it != m_send_group.end())
	{
		// find it
		it->second.recv_num++;
	}
	else
	{
		struct group_info temp;
		temp.group_index = index;
		temp.algorithm_K = K;
		temp.algorithm_N = N;
		temp.recv_num = 1;
		m_send_group.insert(map<uint32_t, group_info>::value_type(index, temp));
	}	
	return 1;
}
/*
int Tunnel::SendGroupInfoBuffer()
{
	if (m_send_group.size() >= FeedbackInfoLen)  // 这里只可能等于
	{
		// 构造数据包
		Ptr<Packet> new_packet = CreateGroupInfoPacket();
		// 发送 ， 在仿真中走控制信令传输通道
		m_token_socket->SendTo(new_packet, 0, InetSocketAddress(m_token_remoteIP, 555)); // 从token 链路中发送	
		for (int i = 0; i < FeedbackInfoLen - FeedbackOverlap; i++)// 清除前面非重复部分
		{
			m_send_group.erase(m_send_group.begin());
		}
	}else
	{
		// 继续，不做处理
	}
}

Ptr<Packet> Tunnel::CreateGroupInfoPacket()
{
	uint8_t send_pac[1024];
	int len = 0;
	memset(send_pac, 0, sizeof(send_pac));
	struct thdr* pac = (struct thdr*)send_pac;
	pac->g_packetindex = 32; // 标定控制数据包
	len += sizeof(struct thdr);
	double rate = total_recv_goodput[total_recv_goodput.size()-1];
	memcpy(send_pac + len, &rate, sizeof(double));  // 填写速率
	len += sizeof(double);
	uint32_t total_num = FeedbackInfoLen;
	memcpy(send_pac + len, &total_num, sizeof(uint32_t)); // 填写长度
	len += sizeof(uint32_t);
	for (auto it = m_send_group.begin(); it != m_send_group.end(); it++)
	{
		uint32_t index = it->first;
		memcpy(send_pac + len, &index, sizeof(uint32_t));
		len += sizeof(uint32_t);                            // 填写序号

		uint8_t k = it->second.algorithm_K;
		memcpy(send_pac + len, &k, sizeof(uint8_t));        // 填写 k
		len += sizeof(uint8_t);

		uint8_t n = it->second.algorithm_N;
		memcpy(send_pac + len, &n, sizeof(uint8_t));        // 填写 n
		len += sizeof(uint8_t);

		uint8_t recv_num = it->second.recv_num;
		memcpy(send_pac + len, &recv_num, sizeof(uint8_t));        // 填写 recv_num
		len += sizeof(uint8_t);

		uint8_t empty = 0;
		memcpy(send_pac + len, &empty, sizeof(uint8_t));        // 填写 0
		len += sizeof(uint8_t);
	}
	Ptr<Packet> new_packet = Create<Packet>(send_pac, len);
	return new_packet;
}
*/

int Tunnel::isExpect(struct pac_info& pac)
{
	uint64_t packet_arrive_time = Simulator::Now().GetMicroSeconds();        // 获取当前的仿真时间	

    if(m_expectGroup == m_recvBuffer.begin()->first)
    {
        if(pac.algorithm_gq_seq == m_recvBuffer.begin()->first)
        {

            return 1;
        }else{
            if((m_recvBuffer.begin())->second.group.size() >= m_recvBuffer.begin()->second.k)
            {
                return 1;
            }else{
                packet_arrive_time = Simulator::Now().GetMicroSeconds();
                //map<uint32_t,uint64_t>::iterator l = m_lastArrive.find((m_recvBuffer.begin())->first);
                if(packet_arrive_time - m_lArrive > m_timeThreshold)
                {
                    cout<<"espg: "<<m_expectGroup<<" rbuf begin: "<<(m_recvBuffer.begin())->first<<" current: "<<pac.algorithm_gq_seq<<endl;
                    cout<<"time out "<<packet_arrive_time - m_lArrive<<" m_time; "<<m_timeThreshold<<endl;
                    return 3;
                }else{
                    return 0;
                }
            }
        }
    }else if(m_expectGroup > (m_recvBuffer.begin())->first)
    {
        map<uint32_t, struct RecvGroup>::iterator target = m_recvBuffer.begin();
        m_recvBuffer.erase(target);
        return 0;
    }else{
        packet_arrive_time = Simulator::Now().GetMicroSeconds();
        //map<uint32_t,uint64_t>::iterator l = m_lastArrive.find((m_recvBuffer.begin())->first);
        if(packet_arrive_time - m_lArrive > m_timeThreshold)
        {
            cout<<"espg: "<<m_expectGroup<<" rbuf begin: "<<(m_recvBuffer.begin())->first<<" current: "<<pac.algorithm_gq_seq<<"time out: "<<packet_arrive_time - m_lArrive<<" m_time: "<<m_timeThreshold<<endl;            
            return 2;
        }
        return 0;       
    }

	return 0;
}

int  Tunnel::PacketDecoding(struct pac_info& pac)
{
        uint32_t index = pac.ppp_index;
        uint64_t lasttime= pac.time;
	if (m_recvBuffer.empty())
	{
		return 0;   // 接收缓存为空
	}
	//uint64_t packet_arrive_time = Simulator::Now().GetMicroSeconds();
	std::map<uint32_t, struct RecvGroup>::iterator target = m_recvBuffer.begin();
	// 首先判断该组数据包是不是期待数据包
	switch (isExpect(pac))
	{
	case 0:
		return 0;
		break;
	case 1:
		//正常情况
		while (RegularPacket(target,index,lasttime))
		{
		}
		break;
	case 2:
		m_expectGroup = m_recvBuffer.begin()->first;
		m_lArrive = Simulator::Now().GetMicroSeconds();
		break;
	case 3: 
		if (target != m_recvBuffer.end())
		{
			while (TimeoutPacket(target,index,lasttime))
			{				
			}
			m_expectGroup = target->first + 1;
			m_lArrive = Simulator::Now().GetMicroSeconds();
			m_recvBuffer.erase(target);
		}
		break;
	}// end switch
	//m_lastArrive = packet_arrive_time; // 所有情况都需要更新last_arrive
	return 1;
}

int Tunnel::RegularPacket(std::map<uint32_t, struct RecvGroup>::iterator target, uint32_t index,uint64_t lasttime)
{
	uint32_t group_k = target->second.k;
	// 接下来,判断分组是否完整
	if (target->second.group.size() < group_k) // 分组不完整，发送单位矩阵
	{
		// 取出第send_num个数据包
		uint32_t num = target->second.sent_num;
		map<uint32_t, struct RecvPacket>::iterator it = target->second.group.begin();
		while (num--)
		{
			it++;
		}
		// 比较，数据包连续，返回1，继续执行，数据包不连续，返回0
		if (it->second.info.algorithm_en_seq == target->second.sent_num&&it != target->second.group.end())
		{
			//接收单位矩阵数据包，一次收一个
			target->second.sent_num++;
			if(FILE_REAL_RECV)
			{
				if(m_index == 1)
				{
					it->second.info.expect_group = m_expectGroup;
					PrintPacketInfo(it->second.info,1);
				}
			}
			ReceiveIM(it,index,lasttime);
			return 1;
		}else
		{
			// 出现不连续数据包，不接收
			return 0;
		}
	}else
	{
		ReceiveRM(target,2,index,lasttime); // 2说明是正常触发的
		m_expectGroup = target->first + 1;
		m_lArrive = Simulator::Now().GetMicroSeconds();
		m_recvBuffer.erase(target);

	}
	return 0;
}

int Tunnel::TimeoutPacket(std::map<uint32_t, struct RecvGroup>::iterator target,uint32_t index,uint64_t lasttime)
{
	uint32_t group_k = target->second.k;
	map<uint32_t, struct RecvPacket>::iterator it;
	// 接下来,判断分组是否完整，如果完整，直接用冗余矩阵解码
	if (target->second.group.size() < group_k) // 分组不完整，发送单位矩阵
	{
		// 取出第send_num个数据包
		uint32_t num = target->second.sent_num;
		it = target->second.group.begin();
		while (num--)
		{
			it++;
		}
		// 比较
		if (it->second.info.algorithm_en_seq <= group_k && it != target->second.group.end())
		{
			//接收单位矩阵数据包，一次收一个
			target->second.sent_num++;
			ReceiveIM(it,index,lasttime);
			return 1;
		}else
		{
			return 0;
		}
	}else
	{
		// 接收冗余数据包，一次接收一组， 这里应该触发不到
		cout << "time out full" << endl;
		//PrintPacketInfo(it->second.info);
		ReceiveRM(target,3,index,lasttime); // 3 说明是超时触发的
	}
	return 0;
}

void Tunnel::CalculateGoodput(uint32_t len,uint32_t index,uint32_t lasttime)
{
	m_pac_num++;
	m_pac_size+=len;
	uint64_t now = Simulator::Now().GetMicroSeconds();
	uint64_t time = now - m_recv_time;
        globlenum[index]+=1;
        float timeinterval=(now-lasttime)/1000000.0;
        timeset.push_back(timeinterval);
        //globletime[i]=(now/1000000.0)%1.0;
	if (time >= 10 * 1000)
	{
		// 开始计算		
		double rate = (m_pac_size * 8 *1000000.0) / (time*1.0);
		total_recv_goodput.push_back(rate);
		if (m_index == 1 && SCREEN_REAL_RATE)
		{
			globledelay[index]=10/(m_pac_num*1.0);
			cout<<lasttime<<endl;
			cout << now / 1000000.0 <<" s\t\t\t" << time / 1000000.0 <<"s\t\t\t"<<"No."<<index<<"\t\t\t"<<globledelay[index]<<"ms\t\t\t"<<rate / 1024 / 1024 << " Mbps \t" <<timeinterval<<"s \t"<<globlenum[0]<<":"<<globlenum[1]<<":"<<globlenum[2]<<endl;	
		}
		if (m_index == 1 && FILE_REAL_RATE)
		{
			file_real_rate << now / 1000000.0 <<"\t" << rate / 1024 / 1024 << endl;
		}
		m_recv_time = now;
		m_pac_num = 0;
		m_pac_size = 0;		
	}
}
int Tunnel::ReceiveIM(map<uint32_t, struct RecvPacket>::iterator it,uint32_t index,uint64_t lasttime)
{
	uint32_t hd_len = sizeof(struct thdr);
	uint32_t len = it->second.info.packet_len - hd_len;
	Ptr<Packet> new_packet = Create<Packet>(it->second.src + hd_len, len);
	m_tun->Receive(new_packet, 0x0800, m_tun->GetAddress(), m_tun->GetAddress(), NetDevice::PACKET_HOST);
	CalculateGoodput(len,index,lasttime);
    AddRecvIMPacInfo(new_packet);

	return 1;
}
int Tunnel::ReceiveRM(std::map<uint32_t, struct RecvGroup>::iterator target, int flag,uint32_t index,uint64_t lasttime)
{
	int n_index = 840; // Guaranteed inverse matrix coefficients are integers
	vector<double> encode_coefficients;
	vector<double> temp_coefficients;
	vector<int> decode_coefficients;
	BIGNUM* encode_packet[7];
	uint8_t decode_data[2048];
	uint32_t group_k = target->second.k;

	map<uint32_t, struct RecvPacket>::iterator send_q;
	for (send_q = target->second.group.begin(); send_q != target->second.group.end(); send_q++)
	{
		for (int k = 0; k < group_k; k++) // n circle
		{
			int seq = send_q->second.info.algorithm_en_seq;
			double temp = EM[group_k - 1][seq][7 - group_k + k];
			encode_coefficients.push_back(temp);

		}
	}
	n_index = detA(encode_coefficients.data(), group_k);
    n_index = abs(n_index);
	LUP_solve_inverse(encode_coefficients, temp_coefficients, n_index, group_k);
	for (int k = 0; k<group_k*group_k; k++) // k*k circle
	{
		decode_coefficients.push_back(round(temp_coefficients[k] * n_index));
	}
	//for (int k = 0; k<group_k; k++) // k circle
	int k = 0;
	for (send_q = target->second.group.begin(); send_q != target->second.group.end(); send_q++)
	{
		uint32_t hd_len = sizeof(struct thdr);
		uint8_t* src = send_q->second.src;
		uint32_t len = send_q->second.info.packet_len;
		encode_packet[k] = BN_new();
		BN_bin2bn(src + hd_len, len- hd_len, encode_packet[k]);
		k++;
	}
	
	BIGNUM* decode_packet;
	decode_packet = BN_new();
	for (int i = 0; i < group_k; i++) // k circle
	{
		BN_zero(decode_packet);
		BIGNUM* inner;
		inner = BN_new();
		for (int j = 0; j < group_k; j++) // k circle
		{
			BN_zero(inner);
			BN_add(inner, inner, encode_packet[j]);
			if (decode_coefficients[i*group_k + j] >= 0)
			{
				BN_ULONG coefficient = decode_coefficients[i*group_k + j];
				BN_mul_word(inner, coefficient);
				BN_add(decode_packet, decode_packet, inner);
			}
			else // Bn_mul_word does not support negative numbers
			{
				BN_ULONG coefficient = abs(decode_coefficients[i*group_k + j]);
				BN_mul_word(inner, coefficient);
				BN_sub(decode_packet, decode_packet, inner);
			}
		}
		BN_free(inner);
		BN_ULONG div = n_index;
		BN_ULONG remainder = BN_div_word(decode_packet, div);
		if (target->second.sent_num ==i) // 只有没有发送过的才能继续发送
		{
			memset(decode_data, 0, 2048);
			int len = BN_bn2bin(decode_packet, decode_data);
			if (remainder != 0)
			{ // 这是解析出错了，否则不会触发
				cout << "index : " << m_index << "\t" << "ReceiveRM " << i << endl;
				cout << remainder << endl;
				cout << "Recv len " << target->second.group[3].info.packet_len << endl;
				cout << "Decode len " << len << endl;
				cout << "Size " << target->second.group.size() << endl;
				//PrintPacketInfo(target->second.group[3].info,flag);
			}
			if(FILE_REAL_RECV)
			{
				if(m_index == 1) // 只处理1号节点接收
				{
					auto iter = target->second.group.begin();
					while(i--)
					{
						iter++;
					}
					iter->second.info.expect_group = m_expectGroup;
					PrintPacketInfo(iter->second.info,flag);
				}
			}
			Ptr<Packet> new_packet = Create<Packet>(decode_data, len);
			m_tun->Receive(new_packet, 0x0800, m_tun->GetAddress(), m_tun->GetAddress(), NetDevice::PACKET_HOST);
			target->second.sent_num++;
			CalculateGoodput(len,index,lasttime);
            AddRecvIMPacInfo(new_packet);
			//pcap_file->Write(Simulator::Now(), new_packet);
		}
		

	}

	BN_free(decode_packet);
	for (int k = 0; k<group_k; k++) // k circle
	{
		if (encode_packet[k])
		BN_free(encode_packet[k]);
	}
}

void Tunnel::PrintAllInfo(ofstream& file,vector<struct pac_info>& data)
{

	// Print Send Information
	for (vector<struct pac_info>::iterator it = data.begin(); it != data.end(); it++)
	{
		file<< (*it).g_packetindex << '\t'
			<< (*it).p_packetindex << '\t'
			<< (int)(*it).ppp_index << '\t'
			<< (*it).time << '\t'
			<< (*it).total_data << '\t'
			<< (*it).queue_len << '\t'
			<< (*it).packet_len << '\t'
			<< (uint32_t)(*it).algorithm_K << '\t'
			<< (uint32_t)(*it).algorithm_N << '\t'
			<< (uint32_t)(*it).algorithm_en_seq << '\t'
			<< (uint32_t)(*it).algorithm_gq_seq << endl;
	}
}


void DelayInequatity(NodeContainer  NodeContainer){
   //cout<<DynamicCast<PointToPointNetDevice>((NodeContainer.Get(0))->GetDevice(0))->GetQueue()<<endl;
   //cout<<"tx array:"<< n0->m_tx[i]->GetNBytes() * 8<<endl;
   //cout<<"laji"<<endl;
}


void DataGetter(NodeContainer c){
struct Info_Abstract abstract_ycy;
FlowMonitorHelper flowhelper;
Ptr<FlowMonitor> monitor = flowhelper.Install(c);
//monitor->StartRightNow();
monitor->Stop(MilliSeconds(5));
monitor->CheckForLostPackets();
Ptr<Ipv4FlowClassifier> classifier = DynamicCast<Ipv4FlowClassifier>(flowhelper.GetClassifier());
std::map<FlowId, FlowMonitor::FlowStats> stats = monitor->GetFlowStats();
for (std::map<FlowId, FlowMonitor::FlowStats>::const_iterator iter = stats.begin(); iter != stats.end(); ++iter)
{
                Ipv4FlowClassifier::FiveTuple t = classifier->FindFlow(iter->first);
                if(t.sourceAddress == Ipv4Address("10.0.1.1"))
                {
                        double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
                        //abstract.real_tx_packets[0] = iter->second.txPackets ;
                        //abstract.real_rx_packets[0] = iter->second.rxPackets;
                        //abstract.real_link_loss[0] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
                        abstract_ycy.real_link_loss[0] = iter->second.lostPackets/iter->second.txPackets;
                        abstract_ycy.real_link_bw[0] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
                        abstract_ycy.real_link_delay[0] = iter->second.delaySum.GetMilliSeconds()/iter->second.rxPackets;
                        //real_link_delay[0]=iter->second.delaySum.GetMilliSeconds()/iter->second.rxPackets;
                        //running_time += use_time;
                }
                if(t.sourceAddress == Ipv4Address("10.0.2.1"))
                {
                        double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
                       // abstract.real_tx_packets[1] = iter->second.txPackets ;
                       // abstract.real_rx_packets[1] = iter->second.rxPackets;
                        //abstract.real_link_loss[1] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
                        abstract_ycy.real_link_loss[1] = iter->second.lostPackets/iter->second.txPackets;
                        abstract_ycy.real_link_bw[1] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
                        abstract_ycy.real_link_delay[1] = iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
                        //real_link_delay[1]=iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
                        //running_time += use_time;
                }
                if(t.sourceAddress == Ipv4Address("10.0.3.1"))
                {
                        double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
                        //abstract.real_tx_packets[2] = iter->second.txPackets ;
                        //abstract.real_rx_packets[2] = iter->second.rxPackets;
                        //abstract.real_link_loss[2] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
                        abstract_ycy.real_link_loss[2] = iter->second.lostPackets/iter->second.txPackets;
                        abstract_ycy.real_link_bw[2] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
                        abstract_ycy.real_link_delay[2] = iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
                        //real_link_delay[2]=iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
                        //running_time += use_time;
                }
}
monitor->StartRightNow();
cout<<"1 loss: "<<abstract_ycy.real_link_loss[0]<<" 1 bw: "<<abstract_ycy.real_link_bw[0]<<" 1 delay: "<<abstract_ycy.real_link_delay[0]<<endl;
cout<<"2 loss: "<<abstract_ycy.real_link_loss[1]<<" 2 bw: "<<abstract_ycy.real_link_bw[1]<<" 2 delay: "<<abstract_ycy.real_link_delay[1]<<endl;
cout<<"3 loss: "<<abstract_ycy.real_link_loss[2]<<" 3 bw: "<<abstract_ycy.real_link_bw[2]<<" 3 delay: "<<abstract_ycy.real_link_delay[2]<<endl;
}



void task(double * delay, double* loss, double* bandwidth,string file_time,double DataRate1,double DataRate2,double DataRate3,double Delay1,double Delay2,double Delay3,double Loss1,double Loss2,double Loss3,int PacketSize)
{
	Config::SetDefault("ns3::TcpSocket::SegmentSize", UintegerValue(1200));
	// 建立仿真拓扑
	NodeContainer c;
	c.Create(4);
	NodeContainer n0n1 = NodeContainer(c.Get(0), c.Get(1));
	NodeContainer n1n2 = NodeContainer(c.Get(1), c.Get(2));
	NodeContainer n2n3 = NodeContainer(c.Get(2), c.Get(3));
	
	vector<TLink*> link_list;
	InternetStackHelper internet;  //  这两句的顺序可能要改
	internet.Install(c);
	for (int i = 0; i < LINKNUM; i++)
	{
		TLink* link = new TLink(i, loss[i], bandwidth[i], delay[i]);
		link->CreateP2PLink(n1n2,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3);
		//link->PrintLinkInfo();
		link_list.push_back(link);
		link->PrintLinkInfo(i,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3);
	}
        //cmd.Parse(argc, argv);
	/*	TLink* link = new TLink(LINKNUM-1, loss[LINKNUM-1], bandwidth[LINKNUM-1], delay[LINKNUM-1]);
		link->CreateP2PLink(n1n2);
		link_list.push_back(link);
		link->PrintLinkInfo();
	*/
        TLink* token_link = new TLink(LINKNUM, 0, 10, 5); // 控制信令的链路
	token_link->CreateP2PLink(n1n2,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3);
	//link_list.push_back(token_link);
	
	PointToPointHelper p2p; // 延伸链路
	p2p.SetDeviceAttribute("DataRate", StringValue("100Mbps"));
	p2p.SetChannelAttribute("Delay", StringValue("15ms"));
	NetDeviceContainer d0d1 = p2p.Install(n0n1);
	NetDeviceContainer d2d3 = p2p.Install(n2n3);

	Ipv4AddressHelper ipv4_01,ipv4_23;
	ipv4_01.SetBase("192.168.1.0", "255.255.255.0");
	ipv4_01.Assign(d0d1);
	ipv4_23.SetBase("192.168.2.0", "255.255.255.0");
	ipv4_23.Assign(d2d3);

	//Ipv4GlobalRoutingHelper::PopulateRoutingTables();
	// 建立隧道
	Tunnel tunnel_n0(n1n2.Get(0), Mac48Address("11:00:06:06:06:01"), Ipv4Address("192.168.0.1"), link_list,0,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3,PacketSize);
	Tunnel tunnel_n1(n1n2.Get(1), Mac48Address("11:00:06:06:06:02"), Ipv4Address("192.168.0.2"), link_list,1,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3,PacketSize);

	/*int max_delay = max((int)Delay1, (int)Delay2);
	max_delay = max(max_delay, (int)Delay3);
	int min_delay = min((int)Delay1, (int)Delay2);
	min_delay = min(min_delay, (int)Delay3);
	tunnel_n0.m_timeThreshold = max(50, 2 * (max_delay - min_delay)) * 1000;	
	tunnel_n1.m_timeThreshold = max(50, 2 * (max_delay - min_delay)) * 1000;	
	tunnel_n0.ppp_sendRate[0] = int(DataRate1);
	tunnel_n0.ppp_sendRate[1] = int(DataRate2);
	tunnel_n0.ppp_sendRate[2] = int(DataRate3);
	tunnel_n1.ppp_sendRate[0] = int(DataRate1);
	tunnel_n1.ppp_sendRate[1] = int(DataRate2);
	tunnel_n1.ppp_sendRate[2] = int(DataRate3);
	if(loss[0] - eps > 0.08)
	{
		tunnel_n0.m_n = 9;
		tunnel_n1.m_n = 9;
	}else if(loss[0] - eps > 0.05)
	{
		tunnel_n0.m_n = 8;
		tunnel_n1.m_n = 8;
	}else if(loss[0] - eps > 0.04){
		tunnel_n0.m_n = 7;
		tunnel_n1.m_n = 7;
	}else if(loss[0] - eps > 0.02){
                tunnel_n0.m_n = 6;
                tunnel_n1.m_n = 6;
        }else if(loss[0] - eps > 0.01){
                tunnel_n0.m_n = 5;
                tunnel_n1.m_n = 5;
        }else{
                tunnel_n0.m_n = 4;
                tunnel_n1.m_n = 4;
        }*/
	 
	// 添加静态路由，不使用系统自动生成的路由
	
	Ptr<Ipv4> ipv4_A = c.Get(0)->GetObject<Ipv4>();
	Ptr<Ipv4> ipv4_B = c.Get(1)->GetObject<Ipv4>();
	Ptr<Ipv4> ipv4_C = c.Get(2)->GetObject<Ipv4>();
	Ptr<Ipv4> ipv4_D = c.Get(3)->GetObject<Ipv4>();

	Ipv4StaticRoutingHelper ipv4RoutingHelper;

	Ptr<Ipv4StaticRouting> staticRoutingA = ipv4RoutingHelper.GetStaticRouting(ipv4_A);
	staticRoutingA->AddHostRouteTo(Ipv4Address("192.168.2.2"), Ipv4Address("192.168.1.2"), 1);

	Ptr<Ipv4StaticRouting> staticRoutingB = ipv4RoutingHelper.GetStaticRouting(ipv4_B);
	staticRoutingB->AddHostRouteTo(Ipv4Address("192.168.2.2"), Ipv4Address("192.168.0.2"), 6);

	Ptr<Ipv4StaticRouting> staticRoutingC = ipv4RoutingHelper.GetStaticRouting(ipv4_C);
	staticRoutingC->AddHostRouteTo(Ipv4Address("192.168.1.1"), Ipv4Address("192.168.0.1"), 6);

	Ptr<Ipv4StaticRouting> staticRoutingD = ipv4RoutingHelper.GetStaticRouting(ipv4_D);
	staticRoutingD->AddHostRouteTo(Ipv4Address("192.168.1.1"), Ipv4Address("192.168.2.1"), 1);

	if(PCAP)
	{
		p2p.EnablePcapAll("TCP_ycy_capture"); // 开启 wireshark 抓包分析
	}
        /*for (int i = 0; i < 20000000; i += 5)
	{
		Simulator::Schedule(MilliSeconds(i), &DelayInequatity, n1n2);
	}*/
        /*
        for (int i = 0; i < 20000000; i += 10)
	{
		Simulator::Schedule(MilliSeconds(i), &DataGetter, c);
	}*/
	// UDP 保活数据包, 必须开启
	UdpEchoServerHelper echoServer(9);
	ApplicationContainer serverApps = echoServer.Install(c.Get(3));
	serverApps.Start(Seconds(0.0));
	serverApps.Stop(Seconds(15.0));
	UdpEchoClientHelper echoClient(Ipv4Address("192.168.2.2"), 9);
	echoClient.SetAttribute("MaxPackets", UintegerValue(15000));
	echoClient.SetAttribute("Interval", TimeValue(MilliSeconds(1)));
	echoClient.SetAttribute("PacketSize", UintegerValue(PacketSize));
	ApplicationContainer clientApps = echoClient.Install(c.Get(0)); 
	clientApps.Start(Seconds(0.0));
	clientApps.Stop(Seconds(15.0));


	// TCP 流量，使用cubic拥塞控制算法
	uint16_t sinkPort = 8080;
	Address sinkAddress(InetSocketAddress(Ipv4Address("192.168.2.2"), sinkPort)); // 接收端
	PacketSinkHelper packetSinkHelper("ns3::TcpSocketFactory", InetSocketAddress(Ipv4Address("192.168.2.2"), sinkPort));
	ApplicationContainer sinkApps = packetSinkHelper.Install(c.Get(3)); 
	sinkApps.Start(Seconds(0.0));
	sinkApps.Stop(Seconds(5));
	TypeId tid = TypeId::LookupByName("ns3::TcpCubic");
	Config::Set("/NodeList/*/$ns3::TcpL4Protocol/SocketType", TypeIdValue(tid));
	Ptr<Socket> ns3TcpSocket = Socket::CreateSocket(c.Get(0), /*tid*/ TcpSocketFactory::GetTypeId());

	// Set the application on the sender with the size of the packets, number of
	// packets to send and the rate to send them at.
	Ptr<MyApp> app = CreateObject<MyApp>();
	app->Setup(ns3TcpSocket, sinkAddress, 1200, 100000000, DataRate("45Mbps"));
	c.Get(0)->AddApplication(app);
	app->SetStartTime(Seconds(0));
	app->SetStopTime(Seconds(15));
	//BandwidthTrace ();
	Simulator::Stop(Seconds(16.0));

	FlowMonitorHelper flowhelper;//Enable flow monitoring on a set of nodes.
	Ptr<FlowMonitor> monitor = flowhelper.Install(c);

        Simulator::Run();
        
	struct Info_Abstract abstract;
        abstract.file = VERSION;
	abstract.time = file_time;
	//for(int i = 0;i<3;i++)
	//{
 	        //abstract.link_delay[i] = delay[i];
		//abstract.link_loss[i] = loss[i];
		//abstract.link_bw[i] = bandwidth[i];
	//}
 	abstract.link_bw[0] = DataRate1;
 	abstract.link_bw[1] = DataRate2;
 	abstract.link_bw[2] = DataRate3;
 	abstract.link_delay[0] = Delay1;
  	abstract.link_delay[1] = Delay2;
        abstract.link_delay[2] = Delay3;
	abstract.link_loss[0] = Loss1;
	abstract.link_loss[1] = Loss2;
	abstract.link_loss[2] = Loss3;
	
	monitor->CheckForLostPackets();
        //Retrieve the FlowClassifier object created by the Install* methods.
	Ptr<Ipv4FlowClassifier> classifier = DynamicCast<Ipv4FlowClassifier>(flowhelper.GetClassifier());
        //std::map<FlowId, FlowStats> ns3::FlowMonitor::GetFlowStats()const
	std::map<FlowId, FlowMonitor::FlowStats> stats = monitor->GetFlowStats();
	//Retrieve all collected the flow statistics. Note, if the FlowMonitor has not stopped monitoring yet, you should call CheckForLostPackets() to make sure all possibly lost packets are accounted for.
   	double total = 0;
	double running_time = 0;
	// 打印平均速率
	// 打印执行flowmonitor的时间
        //cout<<Simulator::Now().GetSeconds()<<endl;
	for (std::map<FlowId, FlowMonitor::FlowStats>::const_iterator iter = stats.begin(); iter != stats.end(); ++iter)
	{
		Ipv4FlowClassifier::FiveTuple t = classifier->FindFlow(iter->first);
		if(t.sourceAddress == Ipv4Address("10.0.1.1"))
		{
			double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
			abstract.real_tx_packets[0] = iter->second.txPackets ;
			abstract.real_rx_packets[0] = iter->second.rxPackets;
			//abstract.real_link_loss[0] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
			abstract.real_link_loss[0] = iter->second.lostPackets/iter->second.txPackets;
			abstract.real_link_bw[0] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
			abstract.real_link_delay[0] = iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			real_link_delay[0]=iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			running_time += use_time;
		}
		if(t.sourceAddress == Ipv4Address("10.0.2.1"))
		{
			double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
			abstract.real_tx_packets[1] = iter->second.txPackets ;
			abstract.real_rx_packets[1] = iter->second.rxPackets;
			//abstract.real_link_loss[1] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
			abstract.real_link_loss[1] = iter->second.lostPackets/iter->second.txPackets;
			abstract.real_link_bw[1] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
			abstract.real_link_delay[1] = iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			real_link_delay[1]=iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			running_time += use_time;
		}
		if(t.sourceAddress == Ipv4Address("10.0.3.1"))
		{
			double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
			abstract.real_tx_packets[2] = iter->second.txPackets ;
			abstract.real_rx_packets[2] = iter->second.rxPackets;
			//abstract.real_link_loss[2] = fabs(iter->second.txPackets - iter->second.rxPackets) / iter->second.txPackets;
			abstract.real_link_loss[2] = iter->second.lostPackets/iter->second.txPackets;
			abstract.real_link_bw[2] = iter->second.rxBytes * 8.0 / use_time / 1024 / 1024;
			abstract.real_link_delay[2] = iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			real_link_delay[2]=iter->second.delaySum.GetMilliSeconds()  / iter->second.rxPackets;
			running_time += use_time;
		}	
		// if(t.sourceAddress == Ipv4Address("192.168.1.1")&&t.destinationPort == 8080)
		// {
		// 	//double use_time = double(iter->second.timeLastRxPacket.GetSeconds() - iter->second.timeFirstTxPacket.GetSeconds());
		// 	abstract.TCP_tx_packets = iter->second.txPackets ;
		// 	abstract.TCP_rx_packets = iter->second.rxPackets;
		// 	abstract.TCP_loss = abs(iter->second.txPackets - iter->second.rxPackets) / 20;
		// 	abstract.TCP_bw = iter->second.txBytes * 8.0 / 20 / 1024 / 1024;
		// 	abstract.TCP_delay = iter->second.delaySum.GetSeconds()  / 20;
		// }		
	}
	double max_value = 0;
	for(auto v : tunnel_n1.total_recv_goodput) 
	{
		if (max_value < v) max_value = v;
	}
	abstract.TCP_max_bw = max_value/ 1024 / 1024;
	Ptr<PacketSink> sink1 = DynamicCast<PacketSink>(sinkApps.Get(0));
	abstract.TCP_tx_packets = tunnel_n0.m_sendIMPac.size();
	abstract.TCP_rx_packets = tunnel_n1.m_recvIMPac.size();
	abstract.TCP_loss = abs(abstract.TCP_tx_packets - abstract.TCP_rx_packets)/abstract.TCP_tx_packets;
	abstract.TCP_bw = (sink1->GetTotalRx() * 8 / 1024 / 1024) / 20.0;
	abstract.TCP_delay = 0;

	Task_Abstract.push_back(abstract);
	//abstract.TCP_tp = (sink1->GetTotalRx() * 8 / 1024 / 1024) / 20.0;
        
	Simulator::Destroy();
	// 打印所有数据
        
	if(FILE_MULTI_SEND)
	{
		tunnel_n0.PrintAllInfo(file_multi_send,tunnel_n0.m_sendPac);
	}
	if(FILE_MULTI_RECV)
	{
		tunnel_n1.PrintAllInfo(file_multi_recv,tunnel_n1.m_recvPac);
	}

	if(SCREEN_ABSTRACT)
	{
		cout << "LINK\tSet BW\tSet Loss\tSet Delay\tReal BW\tReal Loss\tReal Delay\tSendPac\tRecvPac"<<endl;
		for(int i = 0;i<3;i++)
		{
			cout << "link"<<i<<"\t"<<abstract.link_bw[i] <<"\t"
				<<abstract.link_loss[i]<<"\t"
				<<abstract.link_delay[i]<<"\t"
				<<abstract.real_link_bw[i]<<"\t"
				<<abstract.real_link_loss[i]<<"\t"
				<<abstract.real_link_delay[i]<<"\t"
               // <<0<<"\t"
				<<abstract.real_tx_packets[i]<<"\t"
				<<abstract.real_rx_packets[i]<<endl;
		}
/*		cout << "TCP"<<"\t"<<0 <<"\t"
				<<0<<"\t"
				<<0<<"\t\t"
				<<abstract.TCP_bw<<"\t"
				<<abstract.TCP_loss<<"\t\t"
				<<abstract.TCP_delay<<"\t"
                <<abstract.TCP_max_bw<<"\t"
				<<abstract.TCP_tx_packets<<"\t"
				<<abstract.TCP_rx_packets<<endl;
*/
	}
	return;
}


int Print2File(string time)
{
	
	if(FILE_PRINT)
	{
		if(FILE_ABSTRACT)
		{
			string file_name = "SS_Abstract.dat"; // standard simulator
			file_abstrct.open(file_name,ios::app);
		}
		if(FILE_MULTI_SEND)
		{
			string file_name = VERSION;
                        file_name+= "_multi_send_";
			file_name +=time;
			file_name += ".dat";
			file_multi_send.open(file_name,ios::app);
		}
		if(FILE_MULTI_RECV)
		{
			string file_name = VERSION;
               		file_name +="_multi_recv_";
			file_name +=time;
			file_name += ".dat";
			file_multi_recv.open(file_name,ios::app);
		}
		if(FILE_REAL_RECV)
		{
			string file_name = VERSION;
            		file_name +="_real_recv_";
			file_name +=time;
			file_name += ".dat";
			file_real_recv.open(file_name,ios::app);
		}
		if(FILE_REAL_RATE)
		{
			string file_name = VERSION;
            		file_name += "_real_rate_";
			file_name +=time;
			file_name += ".dat";
			file_real_rate.open(file_name,ios::app);
		}

	}
	return 1;
}
int PrintClose()
{
	if(FILE_PRINT)
	{
		if(FILE_ABSTRACT)
		{
			file_abstrct.close();
		}
		if(FILE_MULTI_SEND)
		{
			file_multi_send.close();
		}
		if(FILE_MULTI_RECV)
		{
			file_multi_recv.close();
		}
		if(FILE_REAL_RECV)
		{
			file_real_recv.close();
		}
		if(FILE_REAL_RATE)
		{
			file_real_rate.close();
		}
	}
	return 1;
}
int PrintAbstract()
{
	if(FILE_ABSTRACT)
	{
		for(auto iter = Task_Abstract.begin();iter!= Task_Abstract.end();iter++)
		{
			file_abstrct << iter->file << "\t"
			<<iter->time<<"\n";
			for(int i = 0 ; i < 3 ; i++)
			{
				file_abstrct <<"set bw"<<"\t"<<iter->link_bw[i]<<"\n" 
				<<"set loss"<<"\t"<<iter->link_loss[i]<<"\n"
				<<"set delay"<<"\t"<<iter->link_delay[i]<<"\n";
			}
			/*file_abstrct <<"TCP_BW"<<"\t"<<iter->TCP_bw<<"\n"
			<<"TCP_LOSS"<<"\t"<<iter->TCP_loss<<"\n"
			<<"TCP_DELAY"<<"\t"<<iter->TCP_delay<<"\n"
            <<"TCP_MAX_BW"<<"\t"<<iter->TCP_max_bw<<"\n"
			<<"TCP_TX_PACKETS"<<"\t"<<iter->TCP_tx_packets<<"\n"
			<<"TCP_RX_PACKETS"<<"\t"<<iter->TCP_rx_packets<<"\n";*/
			for(int i = 0;i<3;i++)
			{
				file_abstrct 
				<<"real_bw_"<<i<<"\t"<<iter->real_link_bw[i]<<"\n"
				<<"real_loss_"<<i<<"\t"<<iter->real_link_loss[i]<<"\n"
				<<"real_delay_"<<i<<"\t"<<iter->real_link_delay[i]<<"\n"
				<<"real_tx_packets_"<<i<<"\t"<<iter->real_tx_packets[i]<<"\n"
				<<"real_rx_packets_"<<i<<"\t"<<iter->real_rx_packets[i]<<"\n";
			}
			file_abstrct << "\n";
		}	
	}
	return 0;
}
//static void RxDrop (Ptr<const Packet> p)  //丢包 回调函数  
//{  
//  NS_LOG_UNCOND ("RxDrop at " << Simulator::Now ().GetSeconds ());  
//}
int main(int argc,char* argv[])
{
	srand((int)time(0));
        double DataRate1=50;
        double DataRate2=50;
        double DataRate3=50;
        double Delay1=15;
        double Delay2=15;
        double Delay3=15;
        double Loss1=0.001;
        double Loss2=0.001;
        double Loss3=0.001;
	int PacketSize=1460;
        CommandLine cmd;
        cmd.AddValue("DataRate1","Rate of sending data packet in path 1",DataRate1);
        cmd.AddValue("DataRate2","Rate of sending data packet in path 2",DataRate2);
        cmd.AddValue("DataRate3","Rate of sending data packet in path 3",DataRate3);
        cmd.AddValue("Delay1","Delay of path 1",Delay1);
        cmd.AddValue("Delay2","Delay of path 2",Delay2);
        cmd.AddValue("Delay3","Delay of path 3",Delay3);
        cmd.AddValue("Loss1","Loss of path 1",Loss1);
        cmd.AddValue("Loss2","Loss of path 2",Loss2);
        cmd.AddValue("Loss3","Loss of path 3",Loss3);
        cmd.AddValue("PacketSize","Size of packet",PacketSize);
	cmd.Parse(argc, argv);
	double delay[3] = {15, 15, 15};
	double loss[3] =  { 0.00, 0.000, 0.0001 };
	double bandwidth[3] = { 5, 5, 5 };
	VERSION = "Standard_NC_YCY_v1.0";
	FILE_PRINT = 1;
	PCAP = 0;
	FILE_ABSTRACT = 1;
	FILE_MULTI_SEND = 0;
	FILE_MULTI_RECV = 0;
	FILE_REAL_RECV = 0;
	FILE_SINGLE = 0;
	
	time_t timep;
	time(&timep);
	char tmp[64];
	strftime(tmp, sizeof(tmp), "%m_%d_%H_%M_%S", localtime(&timep));
	string tm = tmp;
	//Ptr<UniformRandomVariable> loss_1 =CreateObject<uniformRandomVariable>();
	//loss_1->SetAttribute ("Min",DoubleValue(0));
	//loss_1->SetAttribute ("Max",DoubleValue(0.001));
	//loss[1]=loss_1;
	Print2File(tm);
	task(delay, loss, bandwidth,tm,DataRate1,DataRate2,DataRate3,Delay1,Delay2,Delay3,Loss1,Loss2,Loss3,PacketSize);

	PrintAbstract();

	PrintClose();
	return 0;
}
