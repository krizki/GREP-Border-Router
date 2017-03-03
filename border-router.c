/*
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */
/**
 * \file
 *         border-router
 * \author
 *         Niclas Finne <nfi@sics.se>
 *         Joakim Eriksson <joakime@sics.se>
 *         Nicolas Tsiftes <nvt@sics.se>
 */

#include "contiki.h"
#include "contiki-lib.h"
#include "contiki-net.h"
#include "net/ip/uip.h"
#include "net/ipv6/uip-ds6.h"
#include "net/ipv6/multicast/uip-mcast6-route.h"
#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/rpl/rpl.h"

#include "net/netstack.h"
#include "dev/button-sensor.h"
#include "dev/slip.h"

#include "net/ipv6/multicast/uip-mcast6-engines.h"
#include "net/ipv6/multicast/uip-mcast6.h"
#include "net/ipv6/multicast/smrf.h"
#include "net/ipv6/multicast/roll-tm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#undef CIPHMODE
#define CIPHMODE	0 /* AES = 0, SkipJack = 1, Default HW Cipher = 2 */

#define ENERG_EN	0 /* 0 or 1 */
#if ENERG_EN
  #include "sys/energest.h"
#endif

#define ID_LENGTH 	4
#define MAXBUFFER	200
#define DEBUG DEBUG_NONE
#include "net/ip/uip-debug.h"

static uip_ipaddr_t prefix;
static uint8_t prefix_set;
static uint8_t buffer[MAXBUFFER];
static uint8_t buflen = 0;
static struct uip_udp_conn *motes_conn;
static struct simple_udp_connection broadcast_connection;
static uint8_t old_type;

#define ENERG_EN		ENERGEST_CONF_ON 	// 0 or 1
#if ENERG_EN
  static long int cpu_start_time, transmit_start_time;
  static long int cpu_time, transmit_time;
#endif

PROCESS(border_router_process, "Border router process");

#if WEBSERVER==0
/* No webserver */
AUTOSTART_PROCESSES(&border_router_process);
#elif WEBSERVER>1
/* Use an external webserver application */
#include "webserver-nogui.h"
AUTOSTART_PROCESSES(&border_router_process,&webserver_nogui_process);
#else
/* Use simple webserver with only one page for minimum footprint.
 * Multiple connections can result in interleaved tcp segments since
 * a single static buffer is used for all segments.
 */
#include "httpd-simple.h"
/* The internal webserver can provide additional information if
 * enough program flash is available.
 */
#define WEBSERVER_CONF_LOADTIME 0
#define WEBSERVER_CONF_FILESTATS 0
#define WEBSERVER_CONF_NEIGHBOR_STATUS 0
/* Adding links requires a larger RAM buffer. To avoid static allocation
 * the stack can be used for formatting; however tcp retransmissions
 * and multiple connections can result in garbled segments.
 * TODO:use PSOCk_GENERATOR_SEND and tcp state storage to fix this.
 */
#define WEBSERVER_CONF_ROUTE_LINKS 0
#if WEBSERVER_CONF_ROUTE_LINKS
  #define BUF_USES_STACK 1
#endif

AUTOSTART_PROCESSES(&border_router_process);

static const char *TOP = "<html><head><title>ContikiRPL</title></head><body>\n";
static const char *BOTTOM = "</body></html>\n";
#if BUF_USES_STACK
static char *bufptr, *bufend;
#define ADD(...) do {                                                   \
    bufptr += snprintf(bufptr, bufend - bufptr, __VA_ARGS__);      \
  } while(0)
#else
static char buf[256];
static int blen;
#define ADD(...) do {                                                   \
    blen += snprintf(&buf[blen], sizeof(buf) - blen, __VA_ARGS__);      \
  } while(0)
#endif

/*---------------------------------------------------------------------------*/
static void
ipaddr_add(const uip_ipaddr_t *addr)
{
  uint16_t a;
  int i, f;
  for(i = 0, f = 0; i < sizeof(uip_ipaddr_t); i += 2) {
    a = (addr->u8[i] << 8) + addr->u8[i + 1];
    if(a == 0 && f >= 0) {
      if(f++ == 0) ADD("::");
    } else {
      if(f > 0) {
        f = -1;
      } else if(i > 0) {
        ADD(":");
      }
      ADD("%x", a);
    }
  }
}
/*---------------------------------------------------------------------------*/
static
PT_THREAD(generate_routes(struct httpd_state *s))
{
  static uip_ds6_route_t *r;
  static uip_ds6_nbr_t *nbr;

  PSOCK_BEGIN(&s->sout);
  SEND_STRING(&s->sout, TOP);
  blen = 0;

  ADD("Neighbors<pre>");
  for(nbr = nbr_table_head(ds6_neighbors);
      nbr != NULL;
      nbr = nbr_table_next(ds6_neighbors, nbr)) {
      ipaddr_add(&nbr->ipaddr);

      ADD("\n");
      if(blen > sizeof(buf) - 45) {
        SEND_STRING(&s->sout, buf);
        blen = 0;
      }
  }
  ADD("</pre>Routes<pre>");
  SEND_STRING(&s->sout, buf);
  blen = 0;

  for(r = uip_ds6_route_head(); r != NULL; r = uip_ds6_route_next(r)) {

    ipaddr_add(&r->ipaddr);

    ADD("/%u (via ", r->length);
    ipaddr_add(uip_ds6_route_nexthop(r));
    if(1 || (r->state.lifetime < 600)) {
      ADD(") %lus\n", (unsigned long)r->state.lifetime);
    } else {
      ADD(")\n");
    }
    SEND_STRING(&s->sout, buf);
    blen = 0;
  }
  ADD("</pre>");

  SEND_STRING(&s->sout, buf);
  SEND_STRING(&s->sout, BOTTOM);

  PSOCK_END(&s->sout);
}
/*---------------------------------------------------------------------------*/
httpd_simple_script_t
httpd_simple_get_script(const char *name)
{

  return generate_routes;
}

#endif /* WEBSERVER */

/*---------------------------------------------------------------------------*/
static void
doMulticast(void)
{
  uip_ipaddr_t addr;

  uip_create_linklocal_allnodes_mcast(&addr);

#if ENERG_EN
  ENERGEST_OFF(ENERGEST_TYPE_TRANSMIT);
  ENERGEST_ON(ENERGEST_TYPE_TRANSMIT);
  transmit_start_time = energest_type_time(ENERGEST_TYPE_TRANSMIT);
#endif
  simple_udp_sendto(&broadcast_connection, buffer, buflen, &addr);

#if ENERG_EN
  transmit_time = energest_type_time(ENERGEST_TYPE_TRANSMIT) - transmit_start_time;
  printf("Time: TRANSMIT %lu\n", transmit_time);
#endif
  /*printf("Sending: %d bytes -> ", buflen);
  uint8_t i;
  for(i = 0; i < buflen; i++) printf("%02x", buffer[i]);
  printf("\n");*/
  buflen = 0;
}
/*---------------------------------------------------------------------------*/
static void
packet_asm(uint8_t *data, uint8_t datalen)
{ 
  uint8_t type = data[0];
  uint8_t headerlen;
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
  uint8_t cipherlen = 32;
  uint8_t padlen = 16;
#elif CIPHMODE == 1
  uint8_t cipherlen = 16;
#endif
  uint8_t nitems = 0;

  if (old_type != type) buflen = 0;
  old_type = type;
  switch (type) {
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
  case 1 : 	headerlen = 1 + 2 * ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * cipherlen + padlen)) doMulticast();
		break;
  case 2 : 	memcpy(buffer, data, datalen);
		buflen = datalen;
		doMulticast();
		break;
  case 3 : 	headerlen = 1 + ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * cipherlen + padlen)) doMulticast();
		break;
  case 4 : 	headerlen = 1 + 2 * ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * (cipherlen + padlen))) doMulticast();
		break;
  case 5 : 	headerlen = 1 + ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * (cipherlen + padlen))) doMulticast();
		break;
  case 6 : 	headerlen = 1 + ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * (cipherlen + padlen))) doMulticast();
		break;
#endif
  case 7 : 	headerlen = 1 + ID_LENGTH + 1;
		nitems = data[headerlen - 1];
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 2, datalen - headerlen - 2);
		  buflen += datalen - 2;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 2, datalen - headerlen - 2);
		  buflen += datalen - headerlen - 2;
		}
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
		if (buflen == (headerlen + (ID_LENGTH * nitems) + 2 * (cipherlen + padlen))) doMulticast();
#elif CIPHMODE == 1
		if (buflen == (headerlen + (ID_LENGTH * nitems) + 2 * cipherlen)) doMulticast();
#endif
		break;
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
  case 9 : 	headerlen = 1;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * ID_LENGTH + 2 * (cipherlen + padlen))) doMulticast();
		break;
  case 10 : 	memcpy(buffer, data, datalen);
		buflen = datalen;
		doMulticast();
		break;
#endif
  case 11 : 	headerlen = 1 + 1;
		nitems = data[headerlen - 1];
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 2, datalen - headerlen - 2);
		  buflen += datalen - 2;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 2, datalen - headerlen - 2);
		  buflen += datalen - headerlen - 2;
		}
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
		if (buflen == (headerlen + 16 * (((ID_LENGTH * nitems) >> 4) + 1))) doMulticast();
#elif CIPHMODE == 1
		if (buflen == (headerlen + 8 * (((ID_LENGTH * nitems) >> 3) + 1))) doMulticast();
#endif
		break;
#if ((CIPHMODE == 0) || (CIPHMODE == 2))
  case 12 : 	headerlen = 1 + ID_LENGTH;
		if (data[headerlen] == 1) {
		  memcpy(buffer, data, headerlen);
		  memcpy(buffer + headerlen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - 1;
		}
		else {
		  memcpy(buffer + buflen, data + headerlen + 1, datalen - headerlen - 1);
		  buflen += datalen - headerlen - 1;
		}
		if (buflen == (headerlen + 2 * cipherlen + padlen)) doMulticast();
		break;
#endif
  default :	memcpy(buffer, data, datalen);
		buflen = datalen;
		doMulticast();
		break;
  }
}
/*---------------------------------------------------------------------------*/
static void
tcpip_handler(void)
{ uint8_t *appdata;
  uint8_t appdatalen;

  if(uip_newdata()) {
    appdata = (uint8_t *)uip_appdata;
    appdatalen = uip_datalen();
    appdata[appdatalen] = 0;
    packet_asm(appdata, appdatalen);
  }
}
/*---------------------------------------------------------------------------*/
static void
print_local_addresses(void)
{
  int i;
  uint8_t state;

  PRINTA("Server IPv6 addresses:\n");
  for(i = 0; i < UIP_DS6_ADDR_NB; i++) {
    state = uip_ds6_if.addr_list[i].state;
    if(uip_ds6_if.addr_list[i].isused &&
       (state == ADDR_TENTATIVE || state == ADDR_PREFERRED)) {
      PRINTA(" ");
      uip_debug_ipaddr_print(&uip_ds6_if.addr_list[i].ipaddr);
      PRINTA("\n");
    }
  }
}
/*---------------------------------------------------------------------------*/
void
request_prefix(void)
{
  /* mess up uip_buf with a dirty request... */
  uip_buf[0] = '?';
  uip_buf[1] = 'P';
  uip_len = 2;
  slip_send();
  uip_len = 0;
}
/*---------------------------------------------------------------------------*/
void
set_prefix_64(uip_ipaddr_t *prefix_64)
{
  rpl_dag_t *dag;
  uip_ipaddr_t ipaddr;
  memcpy(&prefix, prefix_64, 16);
  memcpy(&ipaddr, prefix_64, 16);
  prefix_set = 1;
  uip_ds6_set_addr_iid(&ipaddr, &uip_lladdr);
  uip_ds6_addr_add(&ipaddr, 0, ADDR_AUTOCONF);

  dag = rpl_set_root(RPL_DEFAULT_INSTANCE, &ipaddr);
  if(dag != NULL) {
    rpl_set_prefix(dag, &prefix, 64);
    PRINTF("created a new RPL dag\n");
  }
}
/*---------------------------------------------------------------------------*/
PROCESS_THREAD(border_router_process, ev, data)
{
  static struct etimer et;
  PROCESS_BEGIN();

/* While waiting for the prefix to be sent through the SLIP connection, the future
 * border router can join an existing DAG as a parent or child, or acquire a default
 * router that will later take precedence over the SLIP fallback interface.
 * Prevent that by turning the radio off until we are initialized as a DAG root.
 */
  prefix_set = 0;
  NETSTACK_MAC.off(0);

  PROCESS_PAUSE();

  SENSORS_ACTIVATE(button_sensor);

  PRINTF("RPL-Border router started\n");
#if 0
   /* The border router runs with a 100% duty cycle in order to ensure high
     packet reception rates.
     Note if the MAC RDC is not turned off now, aggressive power management of the
     cpu will interfere with establishing the SLIP connection */
  NETSTACK_MAC.off(1);
#endif

#if ENERG_EN
  ENERGEST_OFF(ENERGEST_TYPE_CPU);
  ENERGEST_ON(ENERGEST_TYPE_CPU);
#endif

  /* Request prefix until it has been received */
  while(!prefix_set) {
    etimer_set(&et, CLOCK_SECOND);
    request_prefix();
    PROCESS_WAIT_EVENT_UNTIL(etimer_expired(&et));
  }

  /* Now turn the radio on, but disable radio duty cycling.
   * Since we are the DAG root, reception delays would constrain mesh throughbut.
   */
  NETSTACK_MAC.off(1);

#if DEBUG || 1
  print_local_addresses();
#endif

  motes_conn = udp_new(NULL, UIP_HTONS(0), NULL);
  udp_bind(motes_conn, UIP_HTONS(3001));
  simple_udp_register(&broadcast_connection, 3001,
                      NULL, 3001, NULL);

  while(1) {
    PROCESS_YIELD();
    if(ev == tcpip_event) {
#if ENERG_EN
      cpu_start_time = energest_type_time(ENERGEST_TYPE_CPU);
#endif
      tcpip_handler();

#if ENERG_EN
      cpu_time = energest_type_time(ENERGEST_TYPE_CPU) - cpu_start_time;
      printf("Time: CPU %lu \n", cpu_time);
#endif
    } else if (ev == sensors_event && data == &button_sensor) {
      PRINTF("Initiating global repair\n");
      rpl_repair_root(RPL_DEFAULT_INSTANCE);
    }
  }

  PROCESS_END();
}
/*---------------------------------------------------------------------------*/
